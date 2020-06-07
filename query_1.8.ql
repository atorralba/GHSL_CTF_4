/** 
* @kind path-problem 
*/
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PartialPathGraph

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

predicate getConstraintsStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(GetConstraintsCall call | 
        step1.asExpr() = call.getQualifier() and
        step2.asExpr() = call 
    )
}

predicate keySetStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(GetConstraintsCall call, MethodAccess keySetCall |
        keySetCall.getCallee().getName() = "keySet" and
        keySetCall.getReceiverType() = call.getType() and
        step1.asExpr() = keySetCall.getQualifier() and
        step2.asExpr() = keySetCall
    )
}

predicate hashSetConstructorStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ConstructorCall call |
        call.getConstructedType().getQualifiedName().matches("java.util.HashSet<%>") and
        step1.asExpr() = call.getArgument(0) and
        step2.asExpr() = call
    )
}

class MyAdittionalTaintSteps extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        getConstraintsStep(step1, step2) or
        keySetStep(step1, step2) or
        hashSetConstructorStep(step1, step2)
    }
}

class MyTaintTrackingConfig extends TaintTracking::Configuration {
    MyTaintTrackingConfig() { this = "MyTaintTrackingConfig" }

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
    override int explorationLimit() { result =  10 }
}

class DebugConstraintValidatorSource extends ConstraintValidatorSource{
    DebugConstraintValidatorSource() {
        this.getDeclaringType().getName() = "SchedulingConstraintSetValidator"
    }
}

from MyTaintTrackingConfig cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
where
  cfg.hasPartialFlow(source, sink, _) and
  exists(DebugConstraintValidatorSource specificSource | source.getNode().asParameter() = specificSource.getParameter(0))
select sink, source, sink, "Partial flow from unsanitized user data"
