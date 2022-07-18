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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.*;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    // source method -> only one type, of which taint it generates
    private final Map<JMethod, Type> sources = Maps.newHybridMap();
    // method -> one or more sinks included
    private final MultiMap<JMethod, Sink> sinks = Maps.newMultiMap();
    // sink -> sink calls in different contexts
    private final MultiMap<Sink, CSCallSite> sinkCalls = Maps.newMultiMap();
    // method -> one or more taint transfers that can happen on
    private final MultiMap<JMethod, TaintTransfer> relevantTransfers = Maps.newMultiMap();
    // taint transfer edge between from and to
    private final MultiMap<CSVar, CSVar> transferEdges = Maps.newMultiMap();
    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
        // do more initialization
        config.getSources().forEach(source -> sources.put(source.method(), source.type()));
        config.getSinks().forEach(sink -> sinks.put(sink.method(), sink));
        config.getTransfers().forEach(transfer -> relevantTransfers.put(transfer.method(), transfer));
    }

    // TODO - finish me
    public void checkAndMarkSourceCall(CSCallSite csCallSite) {
        JMethod method = csCallSite.getCallSite().getMethodRef().resolve();
        if (!sources.containsKey(method)) return;
        Context context = csCallSite.getContext();
        Invoke callSite = csCallSite.getCallSite();
        Type type = sources.get(method);
        Var callSiteRetVar = callSite.getResult();
        CSVar csCallSiteRetVar = csManager.getCSVar(context, callSiteRetVar);
        solver.addWorkList(csCallSiteRetVar, csManager.getCSObj(emptyContext, manager.makeTaint(callSite, type)));
    }

    public void checkAndMarkSinkCall(CSCallSite csCallSite) {
        JMethod method = csCallSite.getCallSite().getMethodRef().resolve();
        if (!sinks.containsKey(method)) return;
        sinks.get(method).forEach(sink -> sinkCalls.put(sink, csCallSite));
    }

    public boolean isTransfer(CSCallSite csCallSite) {
        return !relevantTransfers.get(csCallSite.getCallSite().getMethodRef().resolve()).isEmpty();
    }

    public void checkAndAddTTEdge(CSCallSite csCallSite) {
        Invoke callSite = csCallSite.getCallSite();
        JMethod method = callSite.getMethodRef().resolve();
        if (!relevantTransfers.containsKey(method)) return;
        Context context = csCallSite.getContext();
        Set<TaintTransfer> transfers = relevantTransfers.get(method);
        for (TaintTransfer transfer:transfers) {
            int from = transfer.from();
            int to = transfer.to();
            InvokeExp invokeExp = callSite.getInvokeExp();
            CSVar fromCSVar;
            CSVar toCSVar;
            if (from >=0 && to ==-2) { // from arg to result
                fromCSVar = csManager.getCSVar(context, invokeExp.getArg(from));
                toCSVar = csManager.getCSVar(context, callSite.getResult());
            } else if (from == -1 && to == -2) { // from base to result
                InvokeInstanceExp invokeInstanceExp = (InvokeInstanceExp) invokeExp;
                fromCSVar = csManager.getCSVar(context, invokeInstanceExp.getBase());
                toCSVar = csManager.getCSVar(context, callSite.getResult());
            } else { // from arg to base
                InvokeInstanceExp invokeInstanceExp = (InvokeInstanceExp) invokeExp;
                fromCSVar = csManager.getCSVar(context, invokeExp.getArg(from));
                toCSVar = csManager.getCSVar(context, invokeInstanceExp.getBase());
            }
            if (transferEdges.put(fromCSVar, toCSVar)) {
                PointsToSet fromPTS = fromCSVar.getPointsToSet();
                doTransfer(fromPTS, toCSVar);
            }
        }
    }

    public void doTransfer(PointsToSet fromPTS, CSVar to) {
        PointsToSet taintSet = PointsToSetFactory.make();
        fromPTS.objects().map(CSObj::getObject).filter(manager::isTaint)
                .forEach(taintObj -> {
                    Invoke invoke = manager.getSourceCall(taintObj);
                    Obj transferredTaint = manager.makeTaint(invoke, to.getType());
                    taintSet.addObject(csManager.getCSObj(emptyContext, transferredTaint));
                });
        if (!taintSet.isEmpty()) solver.addWorkList(to, taintSet);
    }

    public void propagateTransfer(CSVar from, PointsToSet pts) {
        transferEdges.get(from).forEach(to -> doTransfer(pts, to));
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        sinks.forEach((method, sink) -> {
            int sinkIndex = sink.index();
            sinkCalls.get(sink).forEach(csCallSite -> {
                Context context = csCallSite.getContext();
                Invoke sinkCall = csCallSite.getCallSite();
                Var arg = sinkCall.getInvokeExp().getArg(sinkIndex);
                result.getPointsToSet(csManager.getCSVar(context, arg)).stream()
                        .map(CSObj::getObject).filter(manager::isTaint)
                        .forEach(obj -> taintFlows.add(new TaintFlow(manager.getSourceCall(obj), sinkCall, sinkIndex)));});
        });
        return taintFlows;
    }
}
