open util/integer 
open util/ordering[NodeId] as nodes
open util/steps[Snapshot]
open util/path[Snapshot]

// User defined elements
    sig NodeId {}


// Snapshot definition
    sig Snapshot extends BaseSnapshot {
        System_Replica2_num : lone NodeId,
        System_children : set NodeId,
        System_Replica1_num : lone NodeId,
        System_counter : one NodeId
    }

/***************************** STATE SPACE ************************************/
    abstract sig SystemState extends StateLabel {}
    abstract sig System extends SystemState {}
    abstract sig System_Replica1 extends System {}
    one sig System_Replica1_NotRunning extends System_Replica1 {}
    one sig System_Replica1_Running extends System_Replica1 {}
    abstract sig System_Replica2 extends System {}
    one sig System_Replica2_NotRunning extends System_Replica2 {}
    one sig System_Replica2_Running extends System_Replica2 {}

/***************************** EVENTS SPACE ***********************************/
    one sig System_Update extends InternalEvent {}
    one sig System_Replica1_Start extends EnvironmentEvent {}
    one sig System_Replica1_Stop extends EnvironmentEvent {}
    one sig System_Replica2_Start extends EnvironmentEvent {}
    one sig System_Replica2_Stop extends EnvironmentEvent {}

/*************************** TRANSITIONS SPACE ********************************/
    one sig System_Replica1_t1 extends TransitionLabel {}
    one sig System_Replica1_t2 extends TransitionLabel {}
    one sig System_Replica1_t3 extends TransitionLabel {}
    one sig System_Replica2_t1 extends TransitionLabel {}
    one sig System_Replica2_t2 extends TransitionLabel {}
    one sig System_Replica2_t3 extends TransitionLabel {}

    // Transition System_Replica1_t1
    pred pre_System_Replica1_t1[s:Snapshot] {
        System_Replica1_NotRunning in s.conf
        s.stable = True => {
            System_Replica1_Start in (s.events & EnvironmentEvent)
        } else {
            System_Replica1_Start in s.events
        }
    }

    pred pos_System_Replica1_t1[s, s':Snapshot] {
        s'.conf = s.conf - exit_System_Replica1_NotRunning[System_Replica1_Running] + enter_System_Replica1_Running[System_Replica1_NotRunning, System_Replica1_Running]
        s'.System_Replica2_num = s.System_Replica2_num
        {
            (s'.System_Replica1_num) = (s.System_counter)
            lt[ (s.System_counter), (s'.System_counter)]
            (s'.System_children) = ((s.System_children) + (s'.System_Replica1_num))
        }
        testIfNextStable[s, s', {System_Update}, System_Replica1_t1] => {
            s'.stable = True
            s.stable = True => {
                no ((s'.events & InternalEvent) - {System_Update})
            } else {
                no ((s'.events & InternalEvent) - {{System_Update} + (InternalEvent & s.events)})
            }
        } else {
            s'.stable = False
            s.stable = True => {
                s'.events & InternalEvent = {System_Update}
                s'.events & EnvironmentEvent = s.events & EnvironmentEvent
            } else {
                s'.events = s.events + {System_Update}
            }
    
        }
    }

    pred System_Replica1_t1[s, s': Snapshot] {
        pre_System_Replica1_t1[s]
        pos_System_Replica1_t1[s, s']
        semantics_System_Replica1_t1[s, s']
    }

    pred enabledAfterStep_System_Replica1_t1[s, s': Snapshot, t: TransitionLabel, genEvents: set InternalEvent] {
        // Preconditions
        System_Replica1_NotRunning in s'.conf
        System_Replica1_Start in (s.events + genEvents)
        // Semantics
        // Bigstep "TAKE_ONE" semantics
        no (s.stable = True => t else (s.taken + t)) & {
            System_Replica1_t3 + 
            System_Replica1_t1 + 
            System_Replica1_t2
        }
    }

    pred semantics_System_Replica1_t1[s, s': Snapshot] {
        (s.stable = True) => {
            // SINGLE semantics
            s'.taken = System_Replica1_t1
        } else {
            // SINGLE semantics
            s'.taken = s.taken + System_Replica1_t1
            // Bigstep "TAKE_ONE" semantics
            no s.taken & {
                System_Replica1_t3 + 
                System_Replica1_t1 + 
                System_Replica1_t2
            }
        }
    }

    // Transition System_Replica1_t2
    pred pre_System_Replica1_t2[s:Snapshot] {
        System_Replica1_Running in s.conf
        s.stable = True => {
            System_Replica1_Stop in (s.events & EnvironmentEvent)
        } else {
            System_Replica1_Stop in s.events
        }
    }

    pred pos_System_Replica1_t2[s, s':Snapshot] {
        s'.conf = s.conf - exit_System_Replica1_Running[System_Replica1_NotRunning] + enter_System_Replica1_NotRunning[System_Replica1_Running, System_Replica1_NotRunning]
        s'.System_Replica2_num = s.System_Replica2_num
        s'.System_children = s.System_children
        s'.System_Replica1_num = s.System_Replica1_num
        s'.System_counter = s.System_counter
        testIfNextStable[s, s', {System_Update}, System_Replica1_t2] => {
            s'.stable = True
            s.stable = True => {
                no ((s'.events & InternalEvent) - {System_Update})
            } else {
                no ((s'.events & InternalEvent) - {{System_Update} + (InternalEvent & s.events)})
            }
        } else {
            s'.stable = False
            s.stable = True => {
                s'.events & InternalEvent = {System_Update}
                s'.events & EnvironmentEvent = s.events & EnvironmentEvent
            } else {
                s'.events = s.events + {System_Update}
            }
    
        }
    }

    pred System_Replica1_t2[s, s': Snapshot] {
        pre_System_Replica1_t2[s]
        pos_System_Replica1_t2[s, s']
        semantics_System_Replica1_t2[s, s']
    }

    pred enabledAfterStep_System_Replica1_t2[s, s': Snapshot, t: TransitionLabel, genEvents: set InternalEvent] {
        // Preconditions
        System_Replica1_Running in s'.conf
        System_Replica1_Stop in (s.events + genEvents)
        // Semantics
        // Bigstep "TAKE_ONE" semantics
        no (s.stable = True => t else (s.taken + t)) & {
            System_Replica1_t3 + 
            System_Replica1_t1 + 
            System_Replica1_t2
        }
    }

    pred semantics_System_Replica1_t2[s, s': Snapshot] {
        (s.stable = True) => {
            // SINGLE semantics
            s'.taken = System_Replica1_t2
        } else {
            // SINGLE semantics
            s'.taken = s.taken + System_Replica1_t2
            // Bigstep "TAKE_ONE" semantics
            no s.taken & {
                System_Replica1_t3 + 
                System_Replica1_t1 + 
                System_Replica1_t2
            }
        }
    }

    // Transition System_Replica1_t3
    pred pre_System_Replica1_t3[s:Snapshot] {
        System_Replica1_Running in s.conf
        s.stable = True => {
            System_Update in (s.events & EnvironmentEvent)
        } else {
            System_Update in s.events
        }
        {
            (s.System_Replica1_num) != ((s.System_children).max)
        }
    }

    pred pos_System_Replica1_t3[s, s':Snapshot] {
        s'.conf = s.conf
        s'.System_Replica2_num = s.System_Replica2_num
        s'.System_Replica1_num = s.System_Replica1_num
        s'.System_counter = s.System_counter
        {
            (s'.System_children) = ((s.System_Replica1_num) + ((s.System_children).max))
        }
        testIfNextStable[s, s', {System_Update}, System_Replica1_t3] => {
            s'.stable = True
            s.stable = True => {
                no ((s'.events & InternalEvent) - {System_Update})
            } else {
                no ((s'.events & InternalEvent) - {{System_Update} + (InternalEvent & s.events)})
            }
        } else {
            s'.stable = False
            s.stable = True => {
                s'.events & InternalEvent = {System_Update}
                s'.events & EnvironmentEvent = s.events & EnvironmentEvent
            } else {
                s'.events = s.events + {System_Update}
            }
    
        }
    }

    pred System_Replica1_t3[s, s': Snapshot] {
        pre_System_Replica1_t3[s]
        pos_System_Replica1_t3[s, s']
        semantics_System_Replica1_t3[s, s']
    }

    pred enabledAfterStep_System_Replica1_t3[s, s': Snapshot, t: TransitionLabel, genEvents: set InternalEvent] {
        // Preconditions
        System_Replica1_Running in s'.conf
        System_Update in (s.events + genEvents)
        {
            (s.System_Replica1_num) != ((s.System_children).max)
        }
        // Semantics
        // Bigstep "TAKE_ONE" semantics
        no (s.stable = True => t else (s.taken + t)) & {
            System_Replica1_t3 + 
            System_Replica1_t1 + 
            System_Replica1_t2
        }
    }

    pred semantics_System_Replica1_t3[s, s': Snapshot] {
        (s.stable = True) => {
            // SINGLE semantics
            s'.taken = System_Replica1_t3
        } else {
            // SINGLE semantics
            s'.taken = s.taken + System_Replica1_t3
            // Bigstep "TAKE_ONE" semantics
            no s.taken & {
                System_Replica1_t3 + 
                System_Replica1_t1 + 
                System_Replica1_t2
            }
        }
    }

    // Transition System_Replica2_t1
    pred pre_System_Replica2_t1[s:Snapshot] {
        System_Replica2_NotRunning in s.conf
        s.stable = True => {
            System_Replica2_Start in (s.events & EnvironmentEvent)
        } else {
            System_Replica2_Start in s.events
        }
    }

    pred pos_System_Replica2_t1[s, s':Snapshot] {
        s'.conf = s.conf - exit_System_Replica2_NotRunning[System_Replica2_Running] + enter_System_Replica2_Running[System_Replica2_NotRunning, System_Replica2_Running]
        s'.System_Replica1_num = s.System_Replica1_num
        {
            (s'.System_Replica2_num) = (s.System_counter)
            lt[ (s.System_counter), (s'.System_counter)]
            (s'.System_children) = ((s.System_children) + (s'.System_Replica2_num))
        }
        testIfNextStable[s, s', {System_Update}, System_Replica2_t1] => {
            s'.stable = True
            s.stable = True => {
                no ((s'.events & InternalEvent) - {System_Update})
            } else {
                no ((s'.events & InternalEvent) - {{System_Update} + (InternalEvent & s.events)})
            }
        } else {
            s'.stable = False
            s.stable = True => {
                s'.events & InternalEvent = {System_Update}
                s'.events & EnvironmentEvent = s.events & EnvironmentEvent
            } else {
                s'.events = s.events + {System_Update}
            }
    
        }
    }

    pred System_Replica2_t1[s, s': Snapshot] {
        pre_System_Replica2_t1[s]
        pos_System_Replica2_t1[s, s']
        semantics_System_Replica2_t1[s, s']
    }

    pred enabledAfterStep_System_Replica2_t1[s, s': Snapshot, t: TransitionLabel, genEvents: set InternalEvent] {
        // Preconditions
        System_Replica2_NotRunning in s'.conf
        System_Replica2_Start in (s.events + genEvents)
        // Semantics
        // Bigstep "TAKE_ONE" semantics
        no (s.stable = True => t else (s.taken + t)) & {
            System_Replica2_t1 + 
            System_Replica2_t3 + 
            System_Replica2_t2
        }
    }

    pred semantics_System_Replica2_t1[s, s': Snapshot] {
        (s.stable = True) => {
            // SINGLE semantics
            s'.taken = System_Replica2_t1
        } else {
            // SINGLE semantics
            s'.taken = s.taken + System_Replica2_t1
            // Bigstep "TAKE_ONE" semantics
            no s.taken & {
                System_Replica2_t1 + 
                System_Replica2_t3 + 
                System_Replica2_t2
            }
        }
    }

    // Transition System_Replica2_t2
    pred pre_System_Replica2_t2[s:Snapshot] {
        System_Replica2_Running in s.conf
        s.stable = True => {
            System_Replica2_Stop in (s.events & EnvironmentEvent)
        } else {
            System_Replica2_Stop in s.events
        }
    }

    pred pos_System_Replica2_t2[s, s':Snapshot] {
        s'.conf = s.conf - exit_System_Replica2_Running[System_Replica2_NotRunning] + enter_System_Replica2_NotRunning[System_Replica2_Running, System_Replica2_NotRunning]
        s'.System_Replica2_num = s.System_Replica2_num
        s'.System_children = s.System_children
        s'.System_Replica1_num = s.System_Replica1_num
        s'.System_counter = s.System_counter
        testIfNextStable[s, s', {System_Update}, System_Replica2_t2] => {
            s'.stable = True
            s.stable = True => {
                no ((s'.events & InternalEvent) - {System_Update})
            } else {
                no ((s'.events & InternalEvent) - {{System_Update} + (InternalEvent & s.events)})
            }
        } else {
            s'.stable = False
            s.stable = True => {
                s'.events & InternalEvent = {System_Update}
                s'.events & EnvironmentEvent = s.events & EnvironmentEvent
            } else {
                s'.events = s.events + {System_Update}
            }
    
        }
    }

    pred System_Replica2_t2[s, s': Snapshot] {
        pre_System_Replica2_t2[s]
        pos_System_Replica2_t2[s, s']
        semantics_System_Replica2_t2[s, s']
    }

    pred enabledAfterStep_System_Replica2_t2[s, s': Snapshot, t: TransitionLabel, genEvents: set InternalEvent] {
        // Preconditions
        System_Replica2_Running in s'.conf
        System_Replica2_Stop in (s.events + genEvents)
        // Semantics
        // Bigstep "TAKE_ONE" semantics
        no (s.stable = True => t else (s.taken + t)) & {
            System_Replica2_t1 + 
            System_Replica2_t3 + 
            System_Replica2_t2
        }
    }

    pred semantics_System_Replica2_t2[s, s': Snapshot] {
        (s.stable = True) => {
            // SINGLE semantics
            s'.taken = System_Replica2_t2
        } else {
            // SINGLE semantics
            s'.taken = s.taken + System_Replica2_t2
            // Bigstep "TAKE_ONE" semantics
            no s.taken & {
                System_Replica2_t1 + 
                System_Replica2_t3 + 
                System_Replica2_t2
            }
        }
    }

    // Transition System_Replica2_t3
    pred pre_System_Replica2_t3[s:Snapshot] {
        System_Replica2_Running in s.conf
        s.stable = True => {
            System_Update in (s.events & EnvironmentEvent)
        } else {
            System_Update in s.events
        }
        {
            (s.System_Replica2_num) != ((s.System_children).max)
        }
    }

    pred pos_System_Replica2_t3[s, s':Snapshot] {
        s'.conf = s.conf
        s'.System_Replica2_num = s.System_Replica2_num
        s'.System_Replica1_num = s.System_Replica1_num
        s'.System_counter = s.System_counter
        {
            (s'.System_children) = ((s.System_Replica2_num) + ((s.System_children).max))
        }
        testIfNextStable[s, s', {System_Update}, System_Replica2_t3] => {
            s'.stable = True
            s.stable = True => {
                no ((s'.events & InternalEvent) - {System_Update})
            } else {
                no ((s'.events & InternalEvent) - {{System_Update} + (InternalEvent & s.events)})
            }
        } else {
            s'.stable = False
            s.stable = True => {
                s'.events & InternalEvent = {System_Update}
                s'.events & EnvironmentEvent = s.events & EnvironmentEvent
            } else {
                s'.events = s.events + {System_Update}
            }
    
        }
    }

    pred System_Replica2_t3[s, s': Snapshot] {
        pre_System_Replica2_t3[s]
        pos_System_Replica2_t3[s, s']
        semantics_System_Replica2_t3[s, s']
    }

    pred enabledAfterStep_System_Replica2_t3[s, s': Snapshot, t: TransitionLabel, genEvents: set InternalEvent] {
        // Preconditions
        System_Replica2_Running in s'.conf
        System_Update in (s.events + genEvents)
        {
            (s.System_Replica2_num) != ((s.System_children).max)
        }
        // Semantics
        // Bigstep "TAKE_ONE" semantics
        no (s.stable = True => t else (s.taken + t)) & {
            System_Replica2_t1 + 
            System_Replica2_t3 + 
            System_Replica2_t2
        }
    }

    pred semantics_System_Replica2_t3[s, s': Snapshot] {
        (s.stable = True) => {
            // SINGLE semantics
            s'.taken = System_Replica2_t3
        } else {
            // SINGLE semantics
            s'.taken = s.taken + System_Replica2_t3
            // Bigstep "TAKE_ONE" semantics
            no s.taken & {
                System_Replica2_t1 + 
                System_Replica2_t3 + 
                System_Replica2_t2
            }
        }
    }


/***************************** ENTER FUNCTIONS ********************************/
    fun enter_State[src, dest: StateLabel]: set StateLabel {
        default_State
    }

    fun enter_System[src, dest: StateLabel]: set System {
        src in StateLabel => init_System[dest]
        else init_System[dest] + enter_State[src, dest]
    }
    
    fun enter_System_Replica1[src, dest: StateLabel]: set System_Replica1 {
        src in System => init_System_Replica1[dest]
        else init_System_Replica1[dest] + enter_System[src, dest]
    }
    
    fun enter_System_Replica1_NotRunning[src, dest: StateLabel]: set System_Replica1_NotRunning {
        src in System_Replica1 => init_System_Replica1_NotRunning[dest]
        else init_System_Replica1_NotRunning[dest] + enter_System_Replica1[src, dest]
    }
    
    fun enter_System_Replica1_Running[src, dest: StateLabel]: set System_Replica1_Running {
        src in System_Replica1 => init_System_Replica1_Running[dest]
        else init_System_Replica1_Running[dest] + enter_System_Replica1[src, dest]
    }
    
    fun enter_System_Replica2[src, dest: StateLabel]: set System_Replica2 {
        src in System => init_System_Replica2[dest]
        else init_System_Replica2[dest] + enter_System[src, dest]
    }
    
    fun enter_System_Replica2_NotRunning[src, dest: StateLabel]: set System_Replica2_NotRunning {
        src in System_Replica2 => init_System_Replica2_NotRunning[dest]
        else init_System_Replica2_NotRunning[dest] + enter_System_Replica2[src, dest]
    }
    
    fun enter_System_Replica2_Running[src, dest: StateLabel]: set System_Replica2_Running {
        src in System_Replica2 => init_System_Replica2_Running[dest]
        else init_System_Replica2_Running[dest] + enter_System_Replica2[src, dest]
    }
    

/**************************** INIT FUNCTIONS **********************************/
    fun init_System[dest: StateLabel]: set System {
        ((!(dest in System_Replica1) or (dest = System_Replica1)) => default_System_Replica1 else none) +
        ((!(dest in System_Replica2) or (dest = System_Replica2)) => default_System_Replica2 else none)
    }
    
    fun init_System_Replica1[dest: StateLabel]: set System_Replica1 {
        ((!(dest in System_Replica1) or (dest = System_Replica1)) => default_System_Replica1 else none)
    }
    
    fun init_System_Replica1_NotRunning[dest: StateLabel]: set System_Replica1_NotRunning {
        ((!(dest in System_Replica1_NotRunning) or (dest = System_Replica1_NotRunning)) => System_Replica1_NotRunning else none)
    }
    
    fun init_System_Replica1_Running[dest: StateLabel]: set System_Replica1_Running {
        ((!(dest in System_Replica1_Running) or (dest = System_Replica1_Running)) => System_Replica1_Running else none)
    }
    
    fun init_System_Replica2[dest: StateLabel]: set System_Replica2 {
        ((!(dest in System_Replica2) or (dest = System_Replica2)) => default_System_Replica2 else none)
    }
    
    fun init_System_Replica2_NotRunning[dest: StateLabel]: set System_Replica2_NotRunning {
        ((!(dest in System_Replica2_NotRunning) or (dest = System_Replica2_NotRunning)) => System_Replica2_NotRunning else none)
    }
    
    fun init_System_Replica2_Running[dest: StateLabel]: set System_Replica2_Running {
        ((!(dest in System_Replica2_Running) or (dest = System_Replica2_Running)) => System_Replica2_Running else none)
    }
    

/***************************** DEFAULT FUNCTIONS ******************************/
    fun default_State: set StateLabel {
        default_System
    }

    fun default_System: set System {
        default_System_Replica1 +
        default_System_Replica2
    }
    
    fun default_System_Replica1: set System_Replica1 {
        System_Replica1_NotRunning
    }
    
    fun default_System_Replica2: set System_Replica2 {
        System_Replica2_NotRunning
    }
    

/****************************** EXIT FUNCTIONS ********************************/
    fun exit_State[dest: StateLabel]: set StateLabel {
        StateLabel
    }

    fun exit_System[dest: StateLabel]: set StateLabel {
        dest in StateLabel => System
        else exit_State[dest]
    }
    
    fun exit_System_Replica1[dest: StateLabel]: set StateLabel {
        dest in System => System_Replica1
        else exit_System[dest]
    }
    
    fun exit_System_Replica1_NotRunning[dest: StateLabel]: set StateLabel {
        dest in System_Replica1 => System_Replica1_NotRunning
        else exit_System_Replica1[dest]
    }
    
    fun exit_System_Replica1_Running[dest: StateLabel]: set StateLabel {
        dest in System_Replica1 => System_Replica1_Running
        else exit_System_Replica1[dest]
    }
    
    fun exit_System_Replica2[dest: StateLabel]: set StateLabel {
        dest in System => System_Replica2
        else exit_System[dest]
    }
    
    fun exit_System_Replica2_NotRunning[dest: StateLabel]: set StateLabel {
        dest in System_Replica2 => System_Replica2_NotRunning
        else exit_System_Replica2[dest]
    }
    
    fun exit_System_Replica2_Running[dest: StateLabel]: set StateLabel {
        dest in System_Replica2 => System_Replica2_Running
        else exit_System_Replica2[dest]
    }
    

/****************************** INITIAL CONDITIONS ****************************/
    pred init[s: Snapshot] {
        s.conf = default_State
        no s.taken
        no s.events & InternalEvent
        // Model specific constraints
        (s.System_counter) = first
            (s.System_children) = none
        (s.System_Replica1_num) = none
        (s.System_Replica2_num) = none
    }

/**************************** SIGNIFICANCE AXIOMS *****************************/
    pred significance {
        steps/reachabilityAxiom
        operationsAxiom
    }

    pred operationsAxiom {
        some s, s': Snapshot | System_Replica1_t1[s, s']
        some s, s': Snapshot | System_Replica1_t2[s, s']
        some s, s': Snapshot | System_Replica1_t3[s, s']
        some s, s': Snapshot | System_Replica2_t1[s, s']
        some s, s': Snapshot | System_Replica2_t2[s, s']
        some s, s': Snapshot | System_Replica2_t3[s, s']
    }

/***************************** MODEL DEFINITION *******************************/
    pred operation[s, s': Snapshot] {
        System_Replica1_t1[s, s'] or
        System_Replica1_t2[s, s'] or
        System_Replica1_t3[s, s'] or
        System_Replica2_t1[s, s'] or
        System_Replica2_t2[s, s'] or
        System_Replica2_t3[s, s']
    }

    pred small_step[s, s': Snapshot] {
        operation[s, s']
    }

    pred testIfNextStable[s, s': Snapshot, genEvents: set InternalEvent, t:TransitionLabel] {
        !enabledAfterStep_System_Replica1_t1[s, s', t, genEvents]
        !enabledAfterStep_System_Replica1_t2[s, s', t, genEvents]
        !enabledAfterStep_System_Replica1_t3[s, s', t, genEvents]
        !enabledAfterStep_System_Replica2_t1[s, s', t, genEvents]
        !enabledAfterStep_System_Replica2_t2[s, s', t, genEvents]
        !enabledAfterStep_System_Replica2_t3[s, s', t, genEvents]
    }

    pred equals[s, s': Snapshot] {
        s'.conf = s.conf
        s'.events = s.events
        s'.taken = s.taken
        // Model specific declarations
        s'.System_Replica2_num = s.System_Replica2_num
        s'.System_children = s.System_children
        s'.System_Replica1_num = s.System_Replica1_num
        s'.System_counter = s.System_counter
    }

    fact {
        all s: Snapshot | s in initial iff init[s]
        all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']
        all s, s': Snapshot | equals[s, s'] => s = s'
        significance
    }





/**************************** Escaped Content *********************************/

run significance for 9 Snapshot, 5 EventLabel, 5 NodeId

fun running[s:Snapshot]: StateLabel {
	s.conf & (System_Replica1_Running + System_Replica2_Running)
}

assert safety {
	//ctl_mc[ag[{s:Snapshot | (#s.System_children).lte[#running[s]]}]]
	p_ctl_mc[p_af[{s:Snapshot | (#s.System_children).lt[#running[s]]}]]
}

//fact { p_finite[ p_ef[not_[{s:Snapshot | (#s.System_children).lte[#running[s]]}]] ] }
// States that are part of the path.
fun pathState: Snapshot { path/pathState }
// A subset of sigma for the path.
fun pathSigma: Snapshot -> Snapshot { path/pathSigma }
check safety for 9 Snapshot, 5 EventLabel, 5 NodeId, 5 Path
