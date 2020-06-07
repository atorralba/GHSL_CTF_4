/** 
* @kind path-problem 
*/
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

class ConstraintValidator extends RefType {
    ConstraintValidator() {
        this.hasQualifiedName("javax.validation", "ConstraintValidator")
    }
}

predicate overridesAConstraintValidatorMethod(Method override) {
    exists(Method base | 
        base.getSourceDeclaration().getDeclaringType() instanceof ConstraintValidator and
        override.overrides(base)
    )
}

class ConstraintValidatorSource extends Method {
	ConstraintValidatorSource() {
        this.getName() = "isValid" and
        overridesAConstraintValidatorMethod(this)
	}
}

class ConstraintValidatorContext extends RefType {
    ConstraintValidatorContext() {
        this.hasQualifiedName("javax.validation", "ConstraintValidatorContext")
    }
}

class ConstraintValidatorContextSink extends MethodAccess {
    ConstraintValidatorContextSink() {
        this.getCallee().getName() = "buildConstraintViolationWithTemplate" and
        this.getCallee().getDeclaringType() instanceof ConstraintValidatorContext
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
}

class GetConstraints extends Method {
    GetConstraints() {
        (
            this.getName() = "getHardConstraints" or
            this.getName() = "getSoftConstraints"
        ) and
        this.getDeclaringType().hasQualifiedName("com.netflix.titus.api.jobmanager.model.job", "Container")
    }
}

class GetConstraintsCall extends MethodAccess {
    GetConstraintsCall() {
        this.getCallee() instanceof GetConstraints
    }
}

predicate hashSetConstructorStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ConstructorCall call |
        call.getConstructedType().getQualifiedName().matches("java.util.HashSet<%>") and
        step1.asExpr() = call.getArgument(0) and
        step2.asExpr() = call
    )
}

class HashSetConstructorTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        hashSetConstructorStep(step1, step2)
    }
}

class ChainableMethod extends Method {
    ChainableMethod() {
        this instanceof GetConstraints or
        this.getName().regexpMatch("keySet|stream|map|collect")
    }
}

predicate chainedCallsOnSourceStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ConstraintValidatorSource origin, MethodAccess chainedCall |
        chainedCall.getQualifier*() = origin.getParameter(0).getAnAccess() and
        chainedCall.getMethod() instanceof ChainableMethod and
        step1.asExpr() = chainedCall.getQualifier() and
        step2.asExpr() = chainedCall
    )
}

class ChainedCallsOnSourceTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        chainedCallsOnSourceStep(step1, step2)
    }
}

class HeuristicGetMessageCall extends MethodAccess {
    HeuristicGetMessageCall() {
        this.getMethod().getName().matches("get%Message")
    }
}

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

predicate throwingCallToGetMessageStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ThrowingCall throwingCall, HeuristicGetMessageCall getMessageCall |
        throwingCall.getCatch().getVariable().getAnAccess() = getMessageCall.getQualifier() and
        step1.asExpr() = throwingCall.getArgument(0) and 
        step2.asExpr() = getMessageCall
    )
}

class ThrowingCallTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        throwingCallToGetMessageStep(step1, step2)
    }
}

from ELInjectionInCustomConstraintValidatorsConfig cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "Custom constraint error message contains unsanitized user data"
