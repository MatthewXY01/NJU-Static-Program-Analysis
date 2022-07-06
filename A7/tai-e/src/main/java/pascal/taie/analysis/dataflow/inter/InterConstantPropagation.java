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
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
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
    // static field -> their store statements
    private Map<JField, Set<StoreField>> storeStaticFieldOn;
    // static field -> their store statements
    private Map<JField, Set<LoadField>> loadStaticFieldOn;
    // base variable of the field -> their store statements
    private Map<Var, Set<StoreField>> storeInstanceFieldOn;
    // base variable of the field -> their load statements
    private Map<Var, Set<LoadField>> loadInstanceFieldOn;
    // base variable of the array -> their store statements
    private Map<Var, Set<StoreArray>> storeArrayOn;
    // base variable of the array -> their load statements
    private Map<Var, Set<LoadArray>> loadArrayOn;
    // variable v -> set of variables, pts of each one within it has intersection with that of v
    private Map<Var, Set<Var>> potentialFieldAliasOf;
    private Map<Var, Set<Var>> potentialArrayAliasOf;

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
        potentialFieldAliasOf = new HybridArrayHashMap<>();
        potentialArrayAliasOf = new HybridArrayHashMap<>();
        // variables involved with field/array access are recorded
        Set<Var> baseInvolvedFieldAccess = new HybridArrayHashSet<>();
        Set<Var> baseInvolvedArrayAccess = new HybridArrayHashSet<>();

        for (Stmt stmt:icfg.getNodes()) {
            if (stmt instanceof StoreField storeField) {
                Var var = storeField.getRValue();
                if (!canHoldInt(var)) continue;
                if (storeField.isStatic()) {
                    storeStaticFieldOn
                            .computeIfAbsent(storeField.getFieldRef().resolve(), set->new HybridArrayHashSet<>())
                            .add(storeField);
                }else {
                    Var base = ((InstanceFieldAccess) storeField.getFieldAccess()).getBase();
                    baseInvolvedFieldAccess.add(base);
                    storeInstanceFieldOn.computeIfAbsent(base, set->new HybridArrayHashSet<>()).add(storeField);
                }
            }else if (stmt instanceof LoadField loadField) {
                Var var = loadField.getLValue();
                if (!canHoldInt(var)) continue;
                if (loadField.isStatic()) {
                    loadStaticFieldOn
                            .computeIfAbsent(loadField.getFieldRef().resolve(), set->new HybridArrayHashSet<>())
                            .add(loadField);
                }else {
                    Var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
                    baseInvolvedFieldAccess.add(base);
                    loadInstanceFieldOn.computeIfAbsent(base, set -> new HybridArrayHashSet<>()).add(loadField);
                }
            }else if (stmt instanceof StoreArray storeArray) {
                Var var = storeArray.getRValue();
                if (!canHoldInt(var))continue;
                Var base = storeArray.getArrayAccess().getBase();
                baseInvolvedArrayAccess.add(base);
                storeArrayOn.computeIfAbsent(base, set->new HybridArrayHashSet<>()).add(storeArray);
            }else if (stmt instanceof LoadArray loadArray) {
                Var var = loadArray.getLValue();
                if (!canHoldInt(var)) continue;
                Var base = loadArray.getArrayAccess().getBase();
                baseInvolvedArrayAccess.add(base);
                loadArrayOn.computeIfAbsent(base, set->new HybridArrayHashSet<>()).add(loadArray);
            }
        }
        // for instance field, we need to search their alias
        for (Var base: baseInvolvedFieldAccess) {
            for (Var aliasBase: baseInvolvedFieldAccess) {
                if (base.equals(aliasBase)){
                    potentialFieldAliasOf.computeIfAbsent(base, set->new HybridArrayHashSet<>()).add(aliasBase);
                }else if (pta.getPointsToSet(base).stream().anyMatch(obj -> pta.getPointsToSet(aliasBase).contains(obj))) {
                    // there is intersection between two points-to set
                    potentialFieldAliasOf.computeIfAbsent(base, set->new HybridArrayHashSet<>()).add(aliasBase);
                }
            }
        }
        for (Var base: baseInvolvedArrayAccess) {
            for (Var aliasBase: baseInvolvedArrayAccess) {
                if (base.equals(aliasBase)){
                    potentialArrayAliasOf.computeIfAbsent(base, set->new HybridArrayHashSet<>()).add(aliasBase);
                }
                if (pta.getPointsToSet(base).stream().anyMatch(obj -> pta.getPointsToSet(aliasBase).contains(obj))) {
                    potentialArrayAliasOf.computeIfAbsent(base, set->new HybridArrayHashSet<>()).add(aliasBase);
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
//        boolean isUpdated = cp.transferNode(storeField, in, out);
        boolean isUpdated = out.copyFrom(in);
        Var x = storeField.getRValue();
        if (isUpdated && ConstantPropagation.canHoldInt(x)) {
            // new stored value, notify relevant load statements
            JField jField = storeField.getFieldRef().resolve();
            if (storeField.isStatic()){
                Set<LoadField> loadStaticSet = loadStaticFieldOn.get(jField);
                if (loadStaticSet!=null)solver.addToUpdate(loadStaticSet);
            }else {
                InstanceFieldAccess fieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();
                Var base = fieldAccess.getBase();
                for (Var aliasBase: potentialFieldAliasOf.get(base)) {
                    Set<LoadField> loadInstanceSet = loadInstanceFieldOn.get(aliasBase);
                    if (loadInstanceSet == null) continue;
                    for (LoadField loadInstance: loadInstanceSet) {
                        if (loadInstance.getFieldRef().resolve().equals(jField)) solver.addToUpdate(loadInstance);
                    }
                }
            }
        }
        return isUpdated;
    }
    protected boolean transferLoadFieldNode(LoadField loadField, CPFact in, CPFact out) {
        Var x = loadField.getLValue();
        // the field can not hold int
        if (!canHoldInt(x)) return out.copyFrom(in);
        CPFact inCopy = in.copy();

        JField jField = loadField.getFieldRef().resolve();
        Value valueFromLoad = Value.getUndef();
        if (loadField.isStatic()) {
            // process the load statement of static fields x = T.f
            Set<StoreField> storeStaticSet = storeStaticFieldOn.get(jField);
            assert storeStaticSet != null;
            for (StoreField storeStatic: storeStaticSet) {
                Var var = storeStatic.getRValue();
                valueFromLoad = cp.meetValue(valueFromLoad, solver.getOutFact(storeStatic).get(var));
            }
        }else {
            // process the load statement of instance fields x = o.f
            InstanceFieldAccess fieldAccess = (InstanceFieldAccess)loadField.getFieldAccess();
            Var base = fieldAccess.getBase();
            // search the aliases
            for (Var aliasBase: potentialFieldAliasOf.get(base)) {
                Set<StoreField> storeInstanceSet = storeInstanceFieldOn.get(aliasBase);
                if (storeInstanceSet == null) continue; // this alias does not store field
                for (StoreField storeInstance: storeInstanceSet) {
                    if (!storeInstance.getFieldRef().resolve().equals(jField))continue;
                    // meet value stored in aliases
                    Var var = storeInstance.getRValue();
                    valueFromLoad = cp.meetValue(valueFromLoad, solver.getOutFact(storeInstance).get(var));
                }
            }
        }
        inCopy.update(x, cp.meetValue(inCopy.get(x), valueFromLoad));
        return out.copyFrom(inCopy);
    }

    protected boolean transferStoreArrayNode(StoreArray storeArray, CPFact in, CPFact out) {
        boolean isUpdated = out.copyFrom(in);
        Var x = storeArray.getRValue();
        if (isUpdated && ConstantPropagation.canHoldInt(x)) {
            Var base = storeArray.getArrayAccess().getBase();
            Var indexVar = storeArray.getArrayAccess().getIndex();
            for (Var aliasBase: potentialArrayAliasOf.get(base)) {
                Set<LoadArray> loadArraySet = loadArrayOn.get(aliasBase);
                if (loadArraySet == null) continue;
                for (LoadArray loadArray: loadArraySet) {
                    Var aliasIndexVar = loadArray.getArrayAccess().getIndex();
                    if (isAliasArrayIndex(in.get(indexVar), solver.getOutFact(loadArray).get(aliasIndexVar))) {
                        solver.addToUpdate(loadArray);
                    }
                }
            }
        }
        return isUpdated;
    }

    protected boolean transferLoadArrayNode(LoadArray loadArray, CPFact in, CPFact out) {
        Var x = loadArray.getLValue();
        if (!ConstantPropagation.canHoldInt(x)) return out.copyFrom(in);
        CPFact inCopy = in.copy();

        Var indexVar = loadArray.getArrayAccess().getIndex();
        Value valueFromLoad = Value.getUndef();
        Var base = loadArray.getArrayAccess().getBase();
        // search the aliases
        for (Var aliasBase : potentialArrayAliasOf.get(base)) {
            Set<StoreArray> storeArraySet = storeArrayOn.get(aliasBase);
            if (storeArraySet == null) continue; // this alias does not store array
            for (StoreArray storeArray: storeArraySet) {
                Var aliasIndexVar = storeArray.getArrayAccess().getIndex();
                if (isAliasArrayIndex(in.get(indexVar), solver.getOutFact(storeArray).get(aliasIndexVar))) {
                    Var var = storeArray.getRValue();
                    valueFromLoad = cp.meetValue(valueFromLoad, solver.getOutFact(storeArray).get(var));
                }
            }
        }
        inCopy.update(x, cp.meetValue(inCopy.get(x), valueFromLoad));
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
            if (canHoldInt(arg)) {
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


    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof ArrayType arrayType && arrayType.elementType() instanceof PrimitiveType primitiveType) {
            switch (primitiveType) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return ConstantPropagation.canHoldInt(var);
    }
    public static boolean isAliasArrayIndex(Value value1, Value value2) {
        if (value1.isUndef() || value2.isUndef())return false;
        if (value1.isConstant() && value2.isConstant()) {
            return value1.getConstant() == value2.getConstant();
        }
        return true;
    }
}
