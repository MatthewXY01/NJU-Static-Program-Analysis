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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.HybridArrayHashMap;
import pascal.taie.util.collection.HybridArrayHashSet;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    // static field -> their store stmts
    private Map<JField, Set<StoreField>> storeStaticFieldOn;
    // static field -> their store stmts
    private Map<JField, Set<LoadField>> loadStaticFieldOn;
    // base variable of the field -> store stmts of the field (and their aliases)
    private Map<Var, Set<StoreField>> storeInstanceFieldOn;
    // base variable of the field -> load stmts of the field (and their aliases)
    private Map<Var, Set<LoadField>> loadInstanceFieldOn;
    // base variable of the array -> store stmts of the array (and their potential (regardless of the index) alases)
    private Map<Var, Set<StoreArray>> storeArrayOn;
    // base variable of the array -> load stmts of the array (and their potential (regardless of the index) alases)
    private Map<Var, Set<LoadArray>> loadArrayOn;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        storeStaticFieldOn = new HybridArrayHashMap<>();
        loadStaticFieldOn = new HybridArrayHashMap<>();
        storeInstanceFieldOn = new HybridArrayHashMap<>();
        loadInstanceFieldOn = new HybridArrayHashMap<>();
        storeArrayOn = new HybridArrayHashMap<>();
        loadArrayOn = new HybridArrayHashMap<>();

        pta.getCallGraph().reachableMethods().forEach(m -> {
            IR ir = m.getIR();
            for (Stmt stmt : ir.getStmts()) {
                if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                    storeStaticFieldOn
                            .computeIfAbsent(storeField.getFieldRef().resolve(), set->new HybridArrayHashSet<>())
                            .add(storeField);
                }else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                    loadStaticFieldOn
                            .computeIfAbsent(loadField.getFieldRef().resolve(), set->new HybridArrayHashSet<>())
                            .add(loadField);
                }
            }
        });
        for (Var base:pta.getVars()){
            for (Var var:pta.getVars()) {
                if (hasIntersection(pta.getPointsToSet(base), pta.getPointsToSet(var))) {
                    // connect store/load statements of array/instance field with corresponding variable.
                    // For each variable, the relevant statements of its aliases
                    // (regardless of the index of array) are also included
                    storeInstanceFieldOn.computeIfAbsent(base, set->new HybridArrayHashSet<>()).addAll(var.getStoreFields());
                    loadInstanceFieldOn.computeIfAbsent(base, set->new HybridArrayHashSet<>()).addAll(var.getLoadFields());
                    storeArrayOn.computeIfAbsent(base, set->new HybridArrayHashSet<>()).addAll(var.getStoreArrays());
                    loadArrayOn.computeIfAbsent(base, set->new HybridArrayHashSet<>()).addAll(var.getLoadArrays());
                }
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
//        return false;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof StoreField storeField) return transferStoreFieldNode(storeField, in, out);
        if (stmt instanceof LoadField loadField) return transferLoadFieldNode(loadField, in, out);
        if (stmt instanceof StoreArray storeArray) return transferStoreArrayNode(storeArray, in, out);
        if (stmt instanceof LoadArray loadArray) return transferLoadArrayNode(loadArray, in, out);
        return cp.transferNode(stmt, in , out);
//        return false;
    }

    protected boolean transferStoreFieldNode(StoreField storeField, CPFact in, CPFact out) {
        boolean isUpdated = out.copyFrom(in);
        Var x = storeField.getRValue();
        if (isUpdated && ConstantPropagation.canHoldInt(x)) {
            // new stored value, notify relevant load statements
            JField jField = storeField.getFieldRef().resolve();
            if (storeField.isStatic()){
                Set<LoadField> loadStaticSet = loadStaticFieldOn.get(jField);
                if (loadStaticSet!=null) solver.workListAdd(loadStaticSet);
            }else {
                InstanceFieldAccess fieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();
                Var base = fieldAccess.getBase();
                Set<LoadField> loadInstanceSet = loadInstanceFieldOn.get(base);
                if (loadInstanceSet != null) {
                    loadInstanceSet.stream()
                            .filter(loadField -> loadField.getFieldRef().resolve().equals(jField))
                            .forEach(solver::workListAdd);
                }
            }
        }
        return isUpdated;
    }

    protected boolean transferLoadFieldNode(LoadField loadField, CPFact in, CPFact out) {
        Var x = loadField.getLValue();
        if (!ConstantPropagation.canHoldInt(x)) return out.copyFrom(in);
        CPFact inCopy = in.copy();

        JField jField = loadField.getFieldRef().resolve();
        if (loadField.isStatic()) {
            // process the load statement of static fields x = T.f
            Set<StoreField> storeStaticSet = storeStaticFieldOn.get(jField);
            if (storeStaticSet != null) {
                storeStaticSet.stream()
                        .map(storeField -> solver.getOutFact(storeField).get(storeField.getRValue()))
                        .reduce(cp::meetValue)
                        .ifPresent(loadedValue -> inCopy.update(x, loadedValue));
            }
        }else {
            // process the load statement of instance fields x = o.f
            InstanceFieldAccess fieldAccess = (InstanceFieldAccess)loadField.getFieldAccess();
            Var base = fieldAccess.getBase();
            Set<StoreField> storeInstanceSet = storeInstanceFieldOn.get(base);
            if (storeInstanceSet != null) {
                storeInstanceSet.stream()
                        .filter(storeField -> jField.equals(storeField.getFieldRef().resolve()))
                        .map(storeField -> solver.getOutFact(storeField).get(storeField.getRValue()))
                        .reduce(cp::meetValue)
                        .ifPresent(loadedValue -> inCopy.update(x, loadedValue));
            }
        }
        return out.copyFrom(inCopy);
    }

    protected boolean transferStoreArrayNode(StoreArray storeArray, CPFact in, CPFact out) {
        boolean isUpdated = out.copyFrom(in);
        Var x = storeArray.getRValue();
        if (isUpdated && ConstantPropagation.canHoldInt(x)) {
            Var base = storeArray.getArrayAccess().getBase();
            Set<LoadArray> loadArraySet = loadArrayOn.get(base);
            if (loadArraySet != null) loadArraySet.forEach(solver::workListAdd);
        }
        return isUpdated;
    }

    protected boolean transferLoadArrayNode(LoadArray loadArray, CPFact in, CPFact out) {
        Var x = loadArray.getLValue();
        if (!ConstantPropagation.canHoldInt(x)) return out.copyFrom(in);
        CPFact inCopy = in.copy();

        Var indexVar = loadArray.getArrayAccess().getIndex();
        Var base = loadArray.getArrayAccess().getBase();
        Set<StoreArray> storeArraySet = storeArrayOn.get(base);
        if (storeArraySet != null) {
            storeArraySet.stream()
                    .filter(storeArray
                            -> isAliasArrayIndex(in.get(indexVar),
                            solver.getOutFact(storeArray).get(storeArray.getArrayAccess().getIndex())))
                    .map(storeArray -> solver.getOutFact(storeArray).get(storeArray.getRValue()))
                    .reduce(cp::meetValue)
                    .ifPresent(value -> inCopy.update(x, value));
        }
        return out.copyFrom(inCopy);
//        return true;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
//        return null;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt callSite = edge.getSource();
        assert callSite instanceof Invoke;
        Invoke invoke = (Invoke) callSite;
        Var var = invoke.getResult();
        if (var != null) {
            CPFact fact = out.copy();
            fact.remove(var);
            return fact;
        }else {
            return out.copy();
        }
//        return null;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact calleeInFact = new CPFact();
        JMethod callee = edge.getCallee();
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        List<Var> argList = invokeExp.getArgs();
        List<Var> paramList = callee.getIR().getParams();
        for (int i = 0; i<argList.size(); i++) {
            Var arg = argList.get(i);
            Var param = paramList.get(i);
            if (ConstantPropagation.canHoldInt(arg)) {
                // also take int array into consideration.
                calleeInFact.update(param, callSiteOut.get(arg));
            }
        }
        return calleeInFact;
//        return null;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact fact = new CPFact();
        Stmt callSite = edge.getCallSite();
        Invoke invoke = ((Invoke)callSite);
        Var var = invoke.getResult();
        if (var == null) return fact;
        edge.getReturnVars()
                .forEach( retVar -> fact.update(var, cp.meetValue(fact.get(var), returnOut.get(retVar))));
        return fact;
//        return null;
    }

    protected  boolean isAliasArrayIndex(Value value1, Value value2) {
        if (value1.isUndef() || value2.isUndef())return false;
        if (value1.isConstant() && value2.isConstant()) {
            return value1.getConstant() == value2.getConstant();
        }
        return true;
    }

    protected boolean hasIntersection (Set<Obj> pts1, Set<Obj> pts2) {
        // if the points-to set of var x is empty and x.f exists,
        // x.f cannot be alias of any pointer, even of itself.
        if (pts1.isEmpty() || pts2.isEmpty()) return false;
        return pts1.stream().anyMatch(pts2::contains);
    }
}
