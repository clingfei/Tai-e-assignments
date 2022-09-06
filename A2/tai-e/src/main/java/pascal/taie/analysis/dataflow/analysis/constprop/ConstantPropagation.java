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

import java.util.Map;
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
        // 初始化为UNDEF？
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (var mapping : fact.entries().toList()) {
            target.update(mapping.getKey(), meetValue(mapping.getValue(), target.get(mapping.getKey())));
        }
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
            return Value.makeConstant(v2.getConstant());
        else if (v2.isUndef())
            return Value.makeConstant(v1.getConstant());
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
        // 实际上CPFact(Map)调用的构造函数new HybridMap最终调用的是 putAll，也是深拷贝，
        CPFact new_out = new CPFact();
        new_out.copyFrom(in);
        /*
         * 首先判断def是否存在以及是否是Var，还要判断是否是Int
         * 删除in中与stmt中redefine的变量
         */
        Optional<LValue> def = stmt.getDef();
        if (def.isPresent() && def.get() instanceof Var) {
            new_out.update((Var) def.get(), Value.getUndef());
            if (canHoldInt((Var) def.get())) {
                DefinitionStmt<?, ?> definitionStmt = (DefinitionStmt<?, ?>)stmt;
                //System.out.println(stmt.getUses().getClass().toString());
//                System.out.println(def.get().toString());
//                System.out.println(def.get().getClass().toString());
//                System.out.println(definitionStmt.getRValue().toString());
//                System.out.println("------------");
                if (definitionStmt.getRValue() instanceof Exp)
                    new_out.update((Var) def.get(), evaluate(definitionStmt.getRValue(), in));
                else
                    new_out.update((Var) def.get(), Value.getNAC());
            } else
                new_out.update((Var) def.get(), Value.getNAC());
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
        } else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            Value op1 = in.get(operand1);
            Value op2 = in.get(operand2);
            String op = ((BinaryExp) exp).getOperator().toString();
            // special case:
            if (op2.isConstant() && op2.getConstant() == 0 && (op.equals("/") || op.equals("%")))
                return Value.getUndef();
            // op1 and op2 均为Constant
            if (op1.isConstant() && op2.isConstant()) {
                switch (op) {
                    case "+":
                        return Value.makeConstant(op1.getConstant() + op2.getConstant());
                    case "-":
                        return Value.makeConstant(op1.getConstant() - op2.getConstant());
                    case "*":
                        return Value.makeConstant(op1.getConstant() * op2.getConstant());
                    case "/":
                        return Value.makeConstant(op1.getConstant() / op2.getConstant());
                    case "%":
                        return Value.makeConstant(op1.getConstant() % op2.getConstant());
                    case "==":
                        return Value.makeConstant(op1.getConstant() == op2.getConstant() ? 1 : 0);
                    case "!=":
                        return Value.makeConstant(op1.getConstant() != op2.getConstant() ? 1 : 0);
                    case "<":
                        return Value.makeConstant(op1.getConstant() < op2.getConstant() ? 1 : 0);
                    case ">":
                        return Value.makeConstant(op1.getConstant() > op2.getConstant() ? 1 : 0);
                    case "<=":
                        return Value.makeConstant(op1.getConstant() <= op2.getConstant() ? 1 : 0);
                    case ">=":
                        return Value.makeConstant(op1.getConstant() >= op2.getConstant() ? 1 : 0);
                    case "<<":
                        return Value.makeConstant(op1.getConstant() << op2.getConstant());
                    case ">>":
                        return Value.makeConstant(op1.getConstant() >> op2.getConstant());
                    case ">>>":
                        return Value.makeConstant(op1.getConstant() >>> op2.getConstant());
                    case "|":
                        return Value.makeConstant(op1.getConstant() | op2.getConstant());
                    case "&":
                        return Value.makeConstant(op1.getConstant() & op2.getConstant());
                    case "^":
                        return Value.makeConstant(op1.getConstant() ^ op2.getConstant());
                }
            } else if (op1.isNAC() || op2.isNAC())
                return Value.getNAC();
            else
                return Value.getUndef();
        } else if (exp.getClass().toString().equals("class pascal.taie.ir.exp.InvokeVirtual")) {
            return Value.getNAC();
        }
        //System.out.println(exp.getClass().toString());
        // otherwise
        return Value.getUndef();
    }
}
