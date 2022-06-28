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
        Set<Stmt> unvisited = new HashSet<>(cfg.getNodes());
        deadCode.addAll(cfg.getNodes());
        Set<Stmt> liveCode = new HashSet<>();
        Stmt entryNode = cfg.getEntry();
        Stmt exitNode = cfg.getExit();
        liveCode.add(exitNode); // exitNode always live
        Stack<Stmt> stack = new Stack<>();
        stack.add(entryNode); // start from entryNode
        unvisited.remove(entryNode);
        while (!stack.isEmpty()) {
            Stmt stmt = stack.pop();
            if (stmt instanceof If ifStmt) {
                // get condition exp
                ConditionExp conditionExp = ifStmt.getCondition();

                // Edge.Kind.IF_FALSE.ordinal(): always false
                // Edge.Kind.IF_TRUE.ordinal(): always true
                // -1: unknown
                int conditionValue = evalConditionExp(ifStmt, conditionExp, constants);
                if (conditionValue >= 0) {
                    // always true or false
                    Edge.Kind targetKind = Edge.Kind.values()[conditionValue];
                    cfg.getOutEdgesOf(ifStmt).forEach( outEdge -> {
                        if (outEdge.getKind() == targetKind)
                            visitStmt(outEdge.getTarget(), unvisited, stack);
                    });
                } else {
                    cfg.getOutEdgesOf(ifStmt).forEach( outEdge -> visitStmt(outEdge.getTarget(), unvisited, stack));
                }
                liveCode.add(ifStmt);
                continue;
            } else if (stmt instanceof SwitchStmt switchStmt) {
                Var switchVar = switchStmt.getVar();
                Value caseAbstractValue = constants.getResult(switchStmt).get(switchVar);
                boolean defaultCaseReachable = true;
                if (caseAbstractValue.isConstant()) {
                    int caseValue = caseAbstractValue.getConstant();
                    Stmt priorityCase = null;
                    for (Pair<Integer, Stmt> caseTargetPair:switchStmt.getCaseTargets()) {
                        if (caseTargetPair.first() == caseValue) {
                            // find the first match
                            defaultCaseReachable = false;
                            priorityCase = caseTargetPair.second();
                            break;
                        }
                    }
                    // NOTE: specific cases may still not exist even caseValue is Constant, thus priorityCase is null.
                    // don't worry, we check the null value and handle the default case uniformly after 'else if'.
                    visitStmt(priorityCase, unvisited, stack);
                } else if (caseAbstractValue.isNAC()){
                    switchStmt.getCaseTargets()
                        .forEach( caseTargetPair -> visitStmt(caseTargetPair.second(), unvisited, stack));
                }
                if (defaultCaseReachable) {
                    visitStmt(switchStmt.getDefaultTarget(), unvisited, stack);
                }
                liveCode.add(switchStmt);
                continue;
            } else if (stmt instanceof AssignStmt<?,?> assignStmt) {
                LValue lValue = assignStmt.getLValue();
                RValue rValue = assignStmt.getRValue();
                if ( !(lValue instanceof Var var && hasNoSideEffect(rValue)) ) {
                    liveCode.add(assignStmt);
                }else if (liveVars.getOutFact(assignStmt).contains(var)){
                    liveCode.add(assignStmt);
                }
            } else {
                liveCode.add(stmt);
            }
            // for the IF and SWITCH Statements, we have checked unreachable branch, code should not reach here.
            for (Stmt sucStmt:cfg.getSuccsOf(stmt)) {
                visitStmt(sucStmt, unvisited, stack);
            }
        }
        deadCode.removeAll(liveCode);

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    public int evalConditionExp(Stmt stmt, ConditionExp exp, DataflowResult<Stmt, CPFact> constants) {
        CPFact fact = constants.getResult(stmt);
        Var opd1 = exp.getOperand1();
        Var opd2 = exp.getOperand2();
        Value opd1AbstractValue = fact.get(opd1);
        Value opd2AbstractValue = fact.get(opd2);
        int ifTrueOrdinal = Edge.Kind.IF_TRUE.ordinal();
        int ifFalseOrdinal = Edge.Kind.IF_FALSE.ordinal();
        ConditionExp.Op op = exp.getOperator();
        if (opd1AbstractValue.isConstant() && opd2AbstractValue.isConstant()) {
            int opd1Value = opd1AbstractValue.getConstant();
            int opd2Value = opd2AbstractValue.getConstant();
            switch (op) {
                case EQ -> {return opd1Value == opd2Value ? ifTrueOrdinal : ifFalseOrdinal;}
                case NE -> {return opd1Value != opd2Value ? ifTrueOrdinal : ifFalseOrdinal;}
                case LT -> {return opd1Value < opd2Value ? ifTrueOrdinal : ifFalseOrdinal;}
                case GT -> {return opd1Value > opd2Value ? ifTrueOrdinal : ifFalseOrdinal;}
                case LE -> {return opd1Value <= opd2Value ? ifTrueOrdinal : ifFalseOrdinal;}
                case GE -> {return opd1Value >= opd2Value ? ifTrueOrdinal : ifFalseOrdinal;}
            }
        }
        return -1;
    }

    public void visitStmt(Stmt stmt, Set<Stmt> unvisited, Stack<Stmt> stack) {
        if (stmt != null && unvisited.remove(stmt)) stack.push(stmt);
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
