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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact boundaryFact = new CPFact();
        cfg.getIR().getParams().forEach(var -> {
            if (canHoldInt(var)) boundaryFact.update(var, Value.getNAC());
        });
        return boundaryFact;
//        return null;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        // according to the implementation of CPFact,
        // setting variable key to UNDEF is equivalent to removing the variable,
        // thus empty initialization is appropriate.
        return new CPFact();
//        return null;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.entries().forEach(varValueEntry -> {
            Var var = varValueEntry.getKey();
            Value newVal = varValueEntry.getValue();
            Value targetVal = target.get(var);
            target.update(var, meetValue(newVal, targetVal));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // NAC meet whatever -> NAC
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        // c meet c -> c; c1 meet c2 -> NAC
        if (v1.isConstant() && v2.isConstant()) return v1.getConstant() == v2.getConstant() ? v1 : Value.getNAC();
        // at most 1 constant -> return it is
        return v1.isConstant() ? v1 : v2;
//        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (! (stmt instanceof DefinitionStmt<?,?>)) return out.copyFrom(in);
        DefinitionStmt<LValue, RValue> defStmt = (DefinitionStmt<LValue, RValue>) stmt;
        LValue lValue = defStmt.getLValue();
        if (!(lValue instanceof Var var && canHoldInt(var))) return out.copyFrom(in);

        CPFact inCopy = in.copy();
        RValue rValue = defStmt.getRValue();
        inCopy.update(var, evaluate(rValue, in));
        return out.copyFrom(inCopy);
//        return false;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        // x=y -> val(y)
        if (exp instanceof Var var) return in.get(var);

        // x=c -> c
        if (exp instanceof IntLiteral intLiteral) return Value.makeConstant(intLiteral.getValue());

        // x=y op z -> ...
        if (exp instanceof BinaryExp binaryExp) {
            Var opd1 = binaryExp.getOperand1();
            Var opd2 = binaryExp.getOperand2();
            Value opd1AbstractValue = in.get(opd1);
            Value opd2AbstractValue = in.get(opd2);
            // any opd is UNDEF -> UNDEF
            if (opd1AbstractValue.isUndef() || opd2AbstractValue.isUndef()) return Value.getUndef();
            // in case that exp=NAC/0, which should return UNDEF,
            // opd1=NAC is not enough to call return
            int opd1Value = 0;
            int opd2Value = 0;
            boolean opd1IsNAC = opd1AbstractValue.isNAC();
            if (!opd1IsNAC) opd1Value = opd1AbstractValue.getConstant();
            if (opd2AbstractValue.isNAC()) return Value.getNAC();
            opd2Value = opd2AbstractValue.getConstant();

            // binary exp is arithmetic exp
            if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                ArithmeticExp.Op op = arithmeticExp.getOperator();
                switch (op) {
                    case ADD -> {
                        if (opd1IsNAC) return Value.getNAC();
                        return Value.makeConstant(opd1Value + opd2Value);
                    }
                    case SUB -> {
                        if (opd1IsNAC) return Value.getNAC();
                        return Value.makeConstant(opd1Value - opd2Value);
                    }
                    case MUL -> {
                        if (opd1IsNAC) return Value.getNAC();
                        return Value.makeConstant(opd1Value * opd2Value);
                    }
                    case DIV -> {
                        // check whether opd2 is the constant 0 first.
                        if (opd2Value == 0) return Value.getUndef();
                        if (opd1IsNAC) return Value.getNAC();
                        return Value.makeConstant(opd1Value / opd2Value);
                    }
                    case REM -> {
                        if (opd2Value == 0) return Value.getUndef();
                        if (opd1IsNAC) return Value.getNAC();
                        return Value.makeConstant(opd1Value % opd2Value);
                    }
                }
            }

            // binary exp other than arithmetic exp
            if (opd1IsNAC) {
                return Value.getNAC();
            }
            if (binaryExp instanceof ConditionExp conditionExp) {
                ConditionExp.Op op = conditionExp.getOperator();
                switch (op) {
                    case EQ -> {return Value.makeConstant(opd1Value == opd2Value ? 1 : 0);}
                    case NE -> {return Value.makeConstant(opd1Value != opd2Value ? 1 : 0);}
                    case LT -> {return Value.makeConstant(opd1Value < opd2Value ? 1 : 0);}
                    case GT -> {return Value.makeConstant(opd1Value > opd2Value ? 1 : 0);}
                    case LE -> {return Value.makeConstant(opd1Value <= opd2Value ? 1 : 0);}
                    case GE -> {return Value.makeConstant(opd1Value >= opd2Value ? 1 : 0);}
                }
            } else if (binaryExp instanceof ShiftExp shiftExp) {
                ShiftExp.Op op = shiftExp.getOperator();
                switch (op) {
                    case SHL -> {return Value.makeConstant(opd1Value << opd2Value);}
                    case SHR -> {return Value.makeConstant(opd1Value >> opd2Value);}
                    case USHR -> {return Value.makeConstant(opd1Value >>> opd2Value);}
                }
            } else if (binaryExp instanceof BitwiseExp bitwiseExp) {
                BitwiseExp.Op op = bitwiseExp.getOperator();
                switch (op) {
                    case OR -> {return Value.makeConstant(opd1Value | opd2Value);}
                    case AND -> {return Value.makeConstant(opd1Value & opd2Value);}
                    case XOR -> {return Value.makeConstant(opd1Value ^ opd2Value);}
                }
            }
        }
        // other unsupported exp such as method invocation
        return Value.getNAC();
//        return null;
    }
}
