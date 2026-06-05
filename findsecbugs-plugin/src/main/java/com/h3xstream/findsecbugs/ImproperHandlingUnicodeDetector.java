/**
 * Find Security Bugs
 * Copyright (c) Philippe Arteau, All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 3.0 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library.
 */
package com.h3xstream.findsecbugs;

import edu.umd.cs.findbugs.BugInstance;
import edu.umd.cs.findbugs.BugReporter;
import edu.umd.cs.findbugs.Priorities;
import edu.umd.cs.findbugs.ba.AnalysisContext;
import edu.umd.cs.findbugs.ba.CFG;
import edu.umd.cs.findbugs.ba.CFGBuilderException;
import edu.umd.cs.findbugs.ba.ClassContext;
import edu.umd.cs.findbugs.ba.Location;
import edu.umd.cs.findbugs.bcel.OpcodeStackDetector;
import org.apache.bcel.Const;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.BootstrapMethod;
import org.apache.bcel.classfile.BootstrapMethods;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantCP;
import org.apache.bcel.classfile.ConstantInvokeDynamic;
import org.apache.bcel.classfile.ConstantMethodHandle;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.INVOKEDYNAMIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;

import java.util.Iterator;

public class ImproperHandlingUnicodeDetector extends OpcodeStackDetector {

    private String IMPROPER_UNICODE_TYPE = "IMPROPER_UNICODE";

    private BugReporter bugReporter;

    public ImproperHandlingUnicodeDetector(BugReporter bugReporter) {
        this.bugReporter = bugReporter;
    }


    private void reportBug() {
        BugInstance bug = new BugInstance(this, IMPROPER_UNICODE_TYPE, Priorities.LOW_PRIORITY) //
                .addClass(this).addMethod(this).addSourceLine(this);
        bugReporter.reportBug(bug);
    }

    /**
     * Resolves the target method that a method reference (an INVOKEDYNAMIC backed by
     * LambdaMetafactory) points to. For example {@code ""::equalsIgnoreCase} compiles to an
     * INVOKEDYNAMIC whose second bootstrap argument is a MethodHandle to
     * {@code java/lang/String.equalsIgnoreCase}.
     *
     * @return The slashed class name and method name of the referenced method,
     *         or {@code null} when the operand is not a LambdaMetafactory method reference.
     */
    private String[] getMethodReferenceTarget(ConstantInvokeDynamic indy) {
        ConstantPool cp = getThisClass().getConstantPool();

        BootstrapMethods bootstrapMethods = null;
        for (Attribute attribute : getThisClass().getAttributes()) {
            if (attribute instanceof BootstrapMethods) {
                bootstrapMethods = (BootstrapMethods) attribute;
                break;
            }
        }
        if (bootstrapMethods == null) {
            return null;
        }

        BootstrapMethod[] methods = bootstrapMethods.getBootstrapMethods();
        int attrIndex = indy.getBootstrapMethodAttrIndex();
        if (attrIndex < 0 || attrIndex >= methods.length) {
            return null;
        }

        // For LambdaMetafactory.metafactory, the bootstrap arguments are:
        // [0] the erased SAM type, [1] the MethodHandle of the implementation, [2] the instantiated type.
        int[] bootstrapArguments = methods[attrIndex].getBootstrapArguments();
        if (bootstrapArguments.length < 2) {
            return null;
        }

        Constant implementation = cp.getConstant(bootstrapArguments[1]);
        if (!(implementation instanceof ConstantMethodHandle)) {
            return null;
        }

        Constant reference = cp.getConstant(((ConstantMethodHandle) implementation).getReferenceIndex());
        if (!(reference instanceof ConstantCP)) {
            return null;
        }
        ConstantCP methodRef = (ConstantCP) reference;

        String className = cp.getConstantString(methodRef.getClassIndex(), Const.CONSTANT_Class);
        ConstantNameAndType nameAndType = cp.getConstant(methodRef.getNameAndTypeIndex());
        String methodName = nameAndType.getName(cp);

        return new String[] { className, methodName };
    }

    /**
     * Uppercase and Lowercase case mapping functions are very common.
     * To avoid massive number of false positives, we check for String comparison done in the same method.
     *
     * @return If the method String.equals() was found in the same method.
     */
    private boolean hasComparisonInMethod() {
        //boolean stringComparisonFound = false;

        ClassContext classCtx = getClassContext();
        ConstantPoolGen cpg = classCtx.getConstantPoolGen();
        CFG cfg;
        try {
            cfg = classCtx.getCFG(getMethod());
        } catch (CFGBuilderException e) {
            AnalysisContext.logError("Cannot get CFG", e);
            return false;
        }

        for (Iterator<Location> i = cfg.locationIterator(); i.hasNext();) {
            Location location = i.next();
            Instruction inst = location.getHandle().getInstruction();
//            ByteCode.printOpCode(inst,cpg);

            if(inst instanceof INVOKEVIRTUAL) {
                INVOKEVIRTUAL inv = (INVOKEVIRTUAL) inst;
                String className = inv.getClassName(cpg);
                String methodName = inv.getMethodName(cpg);
                if(className.equals("java.lang.String") &&
                        (methodName.equals("equals") || methodName.equals("indexOf"))) {
                    return true;
                }
            }
            // The comparison can also be written as a method reference, e.g. "ADMIN"::equals,
            // which compiles to an INVOKEDYNAMIC backed by a LambdaMetafactory method handle.
            else if(inst instanceof INVOKEDYNAMIC) {
                Constant operand = cpg.getConstant(((INVOKEDYNAMIC) inst).getIndex());
                if(operand instanceof ConstantInvokeDynamic) {
                    String[] target = getMethodReferenceTarget((ConstantInvokeDynamic) operand);
                    if(target != null && target[0].equals("java/lang/String") &&
                            (target[1].equals("equals") || target[1].equals("indexOf"))) {
                        return true;
                    }
                }
            }
        }

        return false;
    }

    @Override
    public void sawOpcode(int seen) {
        //printOpCode(seen);

        //        ImproperHandlingUnicodeDetector: [0398]  invokestatic   java/text/Normalizer.normalize (Ljava/lang/CharSequence;Ljava/text/Normalizer$Form;)Ljava/lang/String;
        if (seen == Const.INVOKESTATIC && getClassConstantOperand().equals("java/text/Normalizer")
                && getNameConstantOperand().equals("normalize")) {
            reportBug();
        }
        //        ImproperHandlingUnicodeDetector: [0281]  invokevirtual   java/net/URI.toASCIIString ()Ljava/lang/String;
        else if (seen == Const.INVOKEVIRTUAL && getClassConstantOperand().equals("java/net/URI")
                && getNameConstantOperand().equals("toASCIIString")) {
            reportBug();
        }
        //        ImproperHandlingUnicodeDetector: [0375]  invokestatic   java/net/IDN.toASCII (Ljava/lang/String;)Ljava/lang/String;
        else if (seen == Const.INVOKESTATIC && getClassConstantOperand().equals("java/net/IDN")
                && getNameConstantOperand().equals("toASCII")) {
            reportBug();
        }
        //        ImproperHandlingUnicodeDetector: [0392]  invokevirtual   java/lang/String.toUpperCase ()Ljava/lang/String;
        else if (seen == Const.INVOKEVIRTUAL && getClassConstantOperand().equals("java/lang/String")
                && (getNameConstantOperand().equals("toUpperCase") || getNameConstantOperand().equals("toLowerCase"))) {
            if(hasComparisonInMethod()) {
                reportBug();
            }
        }
        //        ImproperHandlingUnicodeDetector: [0446]  invokevirtual   java/lang/String.equalsIgnoreCase (Ljava/lang/String;)Z
        else if (seen == Const.INVOKEVIRTUAL && getClassConstantOperand().equals("java/lang/String")
                && getNameConstantOperand().equals("equalsIgnoreCase")) {
            reportBug();
        }
        // The same risky calls can be passed as method references, e.g. ""::equalsIgnoreCase or
        // String::toUpperCase. These compile to an INVOKEDYNAMIC whose bootstrap method handle
        // points at the target String method, so the INVOKEVIRTUAL branches above never see them.
        else if (seen == Const.INVOKEDYNAMIC && getConstantRefOperand() instanceof ConstantInvokeDynamic) {
            String[] target = getMethodReferenceTarget((ConstantInvokeDynamic) getConstantRefOperand());
            if (target != null && target[0].equals("java/lang/String")) {
                if (target[1].equals("equalsIgnoreCase")) {
                    reportBug();
                }
                else if ((target[1].equals("toUpperCase") || target[1].equals("toLowerCase"))
                        && hasComparisonInMethod()) {
                    reportBug();
                }
            }
        }

    }

}
