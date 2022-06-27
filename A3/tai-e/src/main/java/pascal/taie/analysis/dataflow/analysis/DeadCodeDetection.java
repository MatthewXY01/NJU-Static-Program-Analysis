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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
//        Set<Stmt> allCode = new HashSet<>(cfg.getNodes());
        deadCode.addAll(cfg.getNodes());
        Set<Stmt> liveCode = new HashSet<>();
        Stmt entryNode = cfg.getEntry();
        liveCode.add(entryNode);
        Stack<Stmt> stack = new Stack<>();
        stack.add(entryNode);
        while (!stack.isEmpty()) {
            Stmt node = stack.pop();
            if (node instanceof If ifStmt) {
                // get condition exp
                ConditionExp conditionExp = ifStmt.getCondition();

                // Edge.Kind.IF_FALSE.ordinal(): always false
                // Edge.Kind.IF_TRUE.ordinal(): always true
                // -1: unknown
                int conditionValue = evalCondition(conditionExp, constants);
                if (conditionValue >= 0) {
                    Edge.Kind targetKind = Edge.Kind.values()[conditionValue];
                    cfg.getOutEdgesOf(ifStmt).forEach( outEdge -> {
                        if (outEdge.getKind() == targetKind) {
                            Stmt targetStmt = outEdge.getTarget();
                            if (liveCode.add(targetStmt)) {
                                stack.push(targetStmt);
                            }
                        }
                    });
                } else {
                    cfg.getOutEdgesOf(ifStmt).forEach( outEdge -> {
                        Stmt targetStmt = outEdge.getTarget();
                        if (liveCode.add(targetStmt)) {
                            stack.push(targetStmt);
                        }
                    });
                }
                continue;
            } else if (node instanceof SwitchStmt switchStmt) {
                Var switchVar = switchStmt.getVar();
                Value caseAbstractValue = constants.getResult(switchStmt).get(switchVar);
                boolean mustReachDefault = true;
                if (caseAbstractValue.isConstant()) {
                    int caseValue = caseAbstractValue.getConstant();
                    Stmt priorityTarget = null;
                    for (Pair<Integer, Stmt> caseTargetPair:switchStmt.getCaseTargets()) {
                        if (caseTargetPair.first().intValue() == caseValue) {
                            mustReachDefault = false;
                            priorityTarget = caseTargetPair.second();
                            break;
                        }
                    }
                    if (priorityTarget != null) {
                        if (liveCode.add(priorityTarget)) {
                            stack.push(priorityTarget);
                        }
                    }
                } else if (caseAbstractValue.isNAC()){
                    switchStmt.getCaseTargets().forEach( caseTargetPair -> {
                        if (liveCode.add(caseTargetPair.second())) {
                            stack.push(caseTargetPair.second());
                        }
                    });
                }
                if (mustReachDefault && switchStmt.getDefaultTarget()!=null) {
                    if (liveCode.add(switchStmt.getDefaultTarget())) {
                        stack.push(switchStmt.getDefaultTarget());
                    }
                }
            } else if (node instanceof AssignStmt<?,?> assignStmt) {
                // TODO
            }
            // Push all successors(not seen yet) of the current node into the stack.
            // For the node that has already killed some successor(s), code should not reach here.
            for (Stmt stmt: cfg.getSuccsOf(node)) {
                if (liveCode.add(stmt)) {
                    stack.push(stmt);
                }
            }
        }
        deadCode.removeAll(liveCode);

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    public int evalCondition(ConditionExp conditionExp, DataflowResult<Stmt, CPFact> constants) {
        return -1;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
