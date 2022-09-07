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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.Optional;

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
        CPFact ret = new CPFact();
        for (var param : cfg.getIR().getParams())
            if (canHoldInt(param))
                ret.update(param, Value.getNAC());
        return ret;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        target.forEach((Var var, Value valTarget) -> { // Mention that `valTarget` cannot be UNDEF
            Value valFact = fact.get(var);
            target.update(var, meetValue(valTarget, valFact));
        });
        // Add the left element in `fact` to `target`
        fact.forEach((Var var, Value valFact) -> { // Mention that `valFact` cannot be UNDEF
            Value valTarget = target.get(var);
            target.update(var, meetValue(valTarget, valFact));
        });
//        for (var mapping : fact.entries().toList()) {
//            target.update(mapping.getKey(), meetValue(mapping.getValue(), target.get(mapping.getKey())));
//        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // NAC ^ v = NAC
        if(v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        // UNDEF ^ v = v
        else if (v1.isUndef() && v2.isUndef())
            return Value.getUndef();
        else if (v1.isUndef())
            return v2;
        else if (v2.isUndef())
            return v1;
        // c ^ c = c
        else if (v1.getConstant() == v2.getConstant())
            return Value.makeConstant(v1.getConstant());
        // c1 ^ c2 = NAC
        else
            return Value.getNAC();
    }

    /*
     * 不能先将in合并到out再计算gen，PPT 245
     */
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact new_out = new CPFact();
        new_out.copyFrom(in);
        /*
         * 首先判断def是否存在以及是否是Var，还要判断是否是Int
         * 删除in中与stmt中redefine的变量
         */
        Optional<LValue> def = stmt.getDef();
        if (def.isPresent() && def.get() instanceof Var) {
            //new_out.update((Var) def.get(), Value.getUndef());
            if (canHoldInt((Var) def.get())) {
                DefinitionStmt<?, ?> definitionStmt = (DefinitionStmt<?, ?>)stmt;
                if (definitionStmt.getRValue() instanceof Exp)
                    new_out.update((Var) def.get(), evaluate(definitionStmt.getRValue(), in));
                else
                    new_out.update((Var) def.get(), Value.getNAC());
            }
        }
        if (new_out.equals(out))
            return true;
        else {
            // clear out or not?
            out.clear();
            out.copyFrom(new_out);
            return false;
        }
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
    /*
     * CPFact is a map, which maps variable to its value.
     * if does not contains mapping from a variable to its value, then the variable is UNDEF.
     *
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        /*
         * 只需要考虑Int类型
         * 只需要处理等号左侧为变量且右侧只能是常量、变量、二元运算表达式的语句, 其他的引用类型忽略其值
         */
        if (exp instanceof Var) {
            return in.get((Var)exp);
        }
        else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof BinaryExp) {
            Value op1 = evaluate(((BinaryExp) exp).getOperand1(), in);
            Value op2 = evaluate(((BinaryExp) exp).getOperand2(), in);
            //Value op1 = in.get(operand1);
            //Value op2 = in.get(operand2);
            String op = ((BinaryExp) exp).getOperator().toString();
            // special case:
            if (op2.isConstant() && op2.getConstant() == 0 && (op.equals("/") || op.equals("%")))
                return Value.getUndef();
            // op1 and op2 均为Constant
            if (op1.isConstant() && op2.isConstant()) {
                return switch (op) {
                    case "+" -> Value.makeConstant(op1.getConstant() + op2.getConstant());
                    case "-" -> Value.makeConstant(op1.getConstant() - op2.getConstant());
                    case "*" -> Value.makeConstant(op1.getConstant() * op2.getConstant());
                    case "/" -> Value.makeConstant(op1.getConstant() / op2.getConstant());
                    case "%" -> Value.makeConstant(op1.getConstant() % op2.getConstant());
                    case "==" -> Value.makeConstant(op1.getConstant() == op2.getConstant() ? 1 : 0);
                    case "!=" -> Value.makeConstant(op1.getConstant() != op2.getConstant() ? 1 : 0);
                    case "<" -> Value.makeConstant(op1.getConstant() < op2.getConstant() ? 1 : 0);
                    case ">" -> Value.makeConstant(op1.getConstant() > op2.getConstant() ? 1 : 0);
                    case "<=" -> Value.makeConstant(op1.getConstant() <= op2.getConstant() ? 1 : 0);
                    case ">=" -> Value.makeConstant(op1.getConstant() >= op2.getConstant() ? 1 : 0);
                    case "<<" -> Value.makeConstant(op1.getConstant() << op2.getConstant());
                    case ">>" -> Value.makeConstant(op1.getConstant() >> op2.getConstant());
                    case ">>>" -> Value.makeConstant(op1.getConstant() >>> op2.getConstant());
                    case "|" -> Value.makeConstant(op1.getConstant() | op2.getConstant());
                    case "&" -> Value.makeConstant(op1.getConstant() & op2.getConstant());
                    case "^" -> Value.makeConstant(op1.getConstant() ^ op2.getConstant());
                    default -> Value.getNAC();
                };
            } else if (op1.isNAC() || op2.isNAC())
                return Value.getNAC();
            else
                return Value.getUndef();
        }
        else
            return Value.getNAC();
    }
}
