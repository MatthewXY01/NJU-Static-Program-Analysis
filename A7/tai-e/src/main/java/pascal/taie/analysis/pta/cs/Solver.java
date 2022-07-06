/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            JMethod method = csMethod.getMethod();
            method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New newStmt) {
            // x = new C()
            Var x = newStmt.getLValue();
            Obj obj = heapModel.getObj(newStmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(heapContext, obj);
            workList.addEntry(csManager.getCSVar(context, x), PointsToSetFactory.make(csObj));
            return null;
        }
        public Void visit(Copy copyStmt) {
            // x = y
            CSVar x = csManager.getCSVar(context, copyStmt.getLValue());
            CSVar y = csManager.getCSVar(context, copyStmt.getRValue());
            addPFGEdge(y, x);
            return null;
        }
        public Void visit(StoreField storeField) {
            // store static field x.f = y
            if (!storeField.isStatic()) return null;
            StaticField field = csManager.getStaticField(storeField.getFieldRef().resolve());
            CSVar y = csManager.getCSVar(context, storeField.getRValue());
            addPFGEdge(y, field);
            return null;
        }
        public Void visit(LoadField loadField) {
            // load static field y = x.f
            if (!loadField.isStatic()) return null;
            StaticField field = csManager.getStaticField(loadField.getFieldRef().resolve());
            CSVar y = csManager.getCSVar(context, loadField.getLValue());
            addPFGEdge(field, y);
            return null;
        }
        public Void visit(Invoke invoke) {
            if (!invoke.isStatic()) return null;
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            JMethod callee = resolveCallee(null, invoke);
            Context calleeContext = contextSelector.selectContext(csCallSite, callee);
            IR ir = callee.getIR();
            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
            List<Var> argList = invoke.getInvokeExp().getArgs();
            List<Var> paramList = ir.getParams();
            assert argList.size() == paramList.size();
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee))) {
                addReachable(csCallee);
                for (int i = 0; i<argList.size(); i++) {
                    CSVar arg = csManager.getCSVar(context, argList.get(i));
                    CSVar param = csManager.getCSVar(calleeContext, paramList.get(i));
                    addPFGEdge(arg, param);
                }
                Var callSiteRetVar = invoke.getLValue();
                if (callSiteRetVar != null) {
                    CSVar csCallSiteRetVar = csManager.getCSVar(context, callSiteRetVar);
                    ir.getReturnVars().stream().map(calleeRetVar -> csManager.getCSVar(calleeContext, calleeRetVar))
                            .forEach(csCalleeRetVar -> addPFGEdge(csCalleeRetVar, csCallSiteRetVar));
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) workList.addEntry(target, pts);
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(ptr, pts);
            if (ptr instanceof CSVar csVar) {
                Context context = csVar.getContext();
                Var x =  csVar.getVar();
                delta.forEach( csObj -> {
                    x.getStoreFields().stream().filter( storeField -> !storeField.isStatic())
                            .forEach( storeInstanceField -> {
                                JField field = storeInstanceField.getFieldRef().resolve();
                                InstanceField csField = csManager.getInstanceField(csObj, field);
                                Var y = storeInstanceField.getRValue();
                                CSVar csY = csManager.getCSVar(context, y);
                                addPFGEdge(csY, csField);
                            });
                    x.getLoadFields().stream().filter( loadField -> !loadField.isStatic())
                            .forEach( loadInstanceField -> {
                                JField field = loadInstanceField.getFieldRef().resolve();
                                InstanceField csField = csManager.getInstanceField(csObj, field);
                                Var y = loadInstanceField.getLValue();
                                CSVar csY = csManager.getCSVar(context, y);
                                addPFGEdge(csField, csY);
                            });
                    x.getStoreArrays().forEach( storeArray -> {
                        ArrayIndex array = csManager.getArrayIndex(csObj);
                        Var y = storeArray.getRValue();
                        CSVar csY = csManager.getCSVar(context, y);
                        addPFGEdge(csY, array);
                    });
                    x.getLoadArrays().forEach( loadArray -> {
                        ArrayIndex array = csManager.getArrayIndex(csObj);
                        Var y = loadArray.getLValue();
                        CSVar csY = csManager.getCSVar(context, y);
                        addPFGEdge(array, csY);
                    });

                    processCall(csVar, csObj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet pt = pointer.getPointsToSet();
        pointsToSet.objects().filter( csObj -> !pt.contains(csObj)).forEach(delta::addObject);
        if (pt.addAll(delta)) {
            pointerFlowGraph.getSuccsOf(pointer).forEach( sucPtr -> workList.addEntry(sucPtr, delta));
        }
        return delta;
//        return null;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var var = recv.getVar();
        Context context = recv.getContext();
        var.getInvokes().stream().filter(invoke -> !invoke.isStatic())
                .forEach( invoke -> {
                    CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
                    JMethod callee = resolveCallee(recvObj, invoke);
                    Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
                    CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                    IR ir = callee.getIR();
                    CSVar csCalleeThis = csManager.getCSVar(calleeContext, ir.getThis());
                    workList.addEntry(csCalleeThis, recv.getPointsToSet());
                    List<Var> argList = invoke.getInvokeExp().getArgs();
                    List<Var> paramList = ir.getParams();
                    if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csCallee))) {
                        addReachable(csCallee);
                        for (int i = 0; i<argList.size(); i++) {
                            CSVar csArg = csManager.getCSVar(context, argList.get(i));
                            CSVar csParam = csManager.getCSVar(calleeContext, paramList.get(i));
                            addPFGEdge(csArg, csParam);
                        }
                        Var callSiteRetVar = invoke.getResult();
                        if (callSiteRetVar != null) {
                            CSVar csCallSiteRetVar = csManager.getCSVar(context, callSiteRetVar);
                            ir.getReturnVars().stream().map(calleeRetVar -> csManager.getCSVar(calleeContext, calleeRetVar))
                                    .forEach( csCalleeRetVar -> addPFGEdge(csCalleeRetVar, csCallSiteRetVar));
                        }
                    }
                });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
