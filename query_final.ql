/** 
* @kind path-problem 
*/
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

/** The ConstraintValidator class */
class ConstraintValidator extends RefType {
    ConstraintValidator() {
        this.hasQualifiedName("javax.validation", "ConstraintValidator")
    }
}

/** Holds if 'override' overrides a method of the ConstraintValidator class */
predicate overridesAConstraintValidatorMethod(Method override) {
    exists(Method base | 
        base.getSourceDeclaration().getDeclaringType() instanceof ConstraintValidator and
        override.overrides(base)
    )
}

/** The isValid method declaration of a class extending ConstraintValidator */
class ConstraintValidatorSource extends Method {
	ConstraintValidatorSource() {
        this.getName() = "isValid" and
        overridesAConstraintValidatorMethod(this)
	}
}

/** ContraintValidatorContext class */
class ConstraintValidatorContext extends RefType {
    ConstraintValidatorContext() {
        this.hasQualifiedName("javax.validation", "ConstraintValidatorContext")
    }
}

/** A call to buildConstraintViolationWithTemplate on an instance of ContraintValidatorContext */
class ConstraintValidatorContextSink extends MethodAccess {
    ConstraintValidatorContextSink() {
        this.getCallee().getName() = "buildConstraintViolationWithTemplate" and
        this.getCallee().getDeclaringType() instanceof ConstraintValidatorContext
    }
}

/** Method declarations of getHardConstraints and getSoftContraints of the Container class */
class GetConstraints extends Method {
    GetConstraints() {
        (
            this.getName() = "getHardConstraints" or
            this.getName() = "getSoftConstraints"
        ) and
        this.getDeclaringType().hasQualifiedName("com.netflix.titus.api.jobmanager.model.job", "Container")
    }
}

/** Calls to getHardConstraints and getSoftContraints */
class GetConstraintsCall extends MethodAccess {
    GetConstraintsCall() {
        this.getCallee() instanceof GetConstraints
    }
}

/** 
 * Holds if there's taint propagation between a HashSetConstructor and its first agument
 */
predicate hashSetConstructorStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ConstructorCall call |
        call.getConstructedType().getQualifiedName().matches("java.util.HashSet<%>") and
        step1.asExpr() = call.getArgument(0) and
        step2.asExpr() = call
    )
}

/** A taint step for HashSet constructors */
class HashSetConstructorTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        hashSetConstructorStep(step1, step2)
    }
}

/** A method which propagates taint between its qualifier and its return value */
class ChainableMethod extends Method {
    ChainableMethod() {
        this instanceof GetConstraints or
        this.getName().regexpMatch("keySet|stream|map|collect")
    }
}

/**
 * Holds if there's taint propagation from our source
 * to the return value of a ChainableMethod called on it (recursively)
 */
predicate chainedCallsOnSourceStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ConstraintValidatorSource origin, MethodAccess chainedCall |
        chainedCall.getQualifier*() = origin.getParameter(0).getAnAccess() and
        chainedCall.getMethod() instanceof ChainableMethod and
        step1.asExpr() = chainedCall.getQualifier() and
        step2.asExpr() = chainedCall
    )
}

/** A taint step for chained calls on a source node */
class ChainedCallsOnSourceTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        chainedCallsOnSourceStep(step1, step2)
    }
}

/**
 * An access to an Exception message (heuristic)
 */
class HeuristicGetMessageCall extends MethodAccess {
    HeuristicGetMessageCall() {
        this.getMethod().getName().matches("get%Message")
    }
}

/**
 * A method call which throws and exception,
 * and that exception is caught by a certain CatchClause
 */
class ThrowingCall extends MethodAccess {
    CatchClause catch;

    ThrowingCall() {
        exists(Exception exception |
            this.getEnclosingStmt().getEnclosingStmt*() = catch.getTry().getBlock() and
            this.getMethod().getSourceDeclaration().getAnException() = exception and
            exception.getType().getAnAncestor() = catch.getACaughtType()
        )
    }
    
    CatchClause getCatch() {
        result = catch
    }
}

/** Holds if a ThrowingCall propagates taint to a HeuristicGetMessageCall call */
predicate throwingCallToGetMessageStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ThrowingCall throwingCall, HeuristicGetMessageCall getMessageCall |
        throwingCall.getCatch().getVariable().getAnAccess() = getMessageCall.getQualifier() and
        step1.asExpr() = throwingCall.getArgument(0) and 
        step2.asExpr() = getMessageCall
    )
}

/** 
 * A taint step for calls which throw an Exception caught
 * in a catch block where the Exception message is accessed
 */
class ThrowingCallTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        throwingCallToGetMessageStep(step1, step2)
    }
}

/** A setter method for a MessageInterpolator in the ValidatorContext class */
class MessageInterpolator extends Method {
    MessageInterpolator() {
        this.getDeclaringType().hasQualifiedName("javax.validation", "ValidatorContext") and
        this.getName() = "messageInterpolator"
    }
}

/** A file containing test code */
class TestFile extends File {
    TestFile(){
        this.getAbsolutePath().matches("%/test/%")
    }
}

/** A MessageInterpolator considered safe -- i.e. doesn't interpolate EL expressions */
class SafeMessageInterpolator extends RefType {
    SafeMessageInterpolator() {
        this.hasQualifiedName("org.hibernate.validator.messageinterpolation", "ParameterMessageInterpolator")
    }
}

/** A call to a method that sets a safe MessageInterpolator  */
class SetSafeMessageInterpolator extends MethodAccess {
    SetSafeMessageInterpolator() {
        this.getCallee() instanceof MessageInterpolator and
        this.getArgument(0).getType() instanceof SafeMessageInterpolator and
        not this.getFile() instanceof TestFile
    }
}

class ELInjectionInCustomConstraintValidatorsConfig extends TaintTracking::Configuration {
    ELInjectionInCustomConstraintValidatorsConfig() { this = "ELInjectionInCustomConstraintValidatorsConfig" }

    override predicate isSource(DataFlow::Node source) { 
        exists(ConstraintValidatorSource isValid | 
            source.asParameter() = isValid.getParameter(0)
        )
    }

    override predicate isSink(DataFlow::Node sink) { 
        exists(ConstraintValidatorContextSink buildWithTemplate |
            sink.asExpr() = buildWithTemplate.getArgument(0)
        )
    }

    override predicate hasFlowPath(DataFlow::PathNode source, DataFlow::PathNode sink) {
        super.hasFlowPath(source, sink) and
        not exists(SetSafeMessageInterpolator safe)
    }
}

from ELInjectionInCustomConstraintValidatorsConfig cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "Custom constraint error message contains unsanitized user data"
