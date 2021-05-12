;; global variables ===========================================================
(defglobal ; these global variables encode the strength of desires
  ?*veryhigh* = 5
  ?*high* = 4
  ?*medium* =  3
  ?*low* = 2 
  ?*verylow* = 1 )

;; templates =================================================================
(deftemplate hunter "A hunter"
  (slot agent (default Xena))
  (slot x (type INTEGER))
  (slot y (type INTEGER))
  (slot gold (default 0)(type INTEGER))
  (slot alive (default TRUE)))

(deftemplate desire "a hunter's desires"
  (slot agent)
  (slot strength (type INTEGER))
  (slot action)
  (slot x)
  (slot y))

(deftemplate goal "a hunter's goals"
  (slot agent)
  (slot action)
  (slot x)
  (slot y))

(deftemplate cave
  "Cave objects store the hunter's model of the world"
  (slot x (type INTEGER))               ; (x,y) coordinates of cave
  (slot y (type INTEGER))               ;
  (slot fromx (default -1))             ; coordinates of the cave from which we 
  (slot fromy (default -1))             ;   first entered the cave.
  (slot visited (default FALSE))        ; Has the hunter been in it?
  (slot stench (default UNKNOWN))       ; Does the cave smell?
  (slot breeze (default UNKNOWN))       ; Is it breezy?
  (slot glitter (default UNKNOWN))      ; Is there a glitter in it?
  (slot has-wumpus (default UNKNOWN))   ; Is there a wumpus here?
  (slot has-pit (default UNKNOWN))      ; Is there a pit here?
  (slot has-gold (default UNKNOWN))     ; Is their gold here?
  (slot has-exit (default UNKNOWN))
  (slot safe (default UNKNOWN)))        ; Is the cave safe -- no wumpus, no pit?

(deftemplate nocave
  "a nocave assertion is used to indicate a cell in the world that is
  not a cave.  (nocave (x 3)(y 3)) means that (3,3) is not a cave."
  (slot x (type INTEGER))
  (slot y (type INTEGER)))

(deftemplate wumpus "a wumpus"
  (slot x (type INTEGER))
  (slot y (type INTEGER))
  (slot alive (default TRUE)))

(deftemplate pit "A pit"
  (slot x (type INTEGER))
  (slot y (type INTEGER)))

(deftemplate gold "Gold has a location and amount."
  (slot x (type INTEGER))
  (slot y (type INTEGER))
  (slot amount (type INTEGER)(default 10)))

(deftemplate exit "coordinates of the entrance/exit to the caves."
  (slot x)
  (slot y))

;; functions =================================================================
(deffunction buildworld (?width ?height)
  ;; (buildworld N M) makes cave assertions for a NxM rectangular  world.
  (printout t "Adding adj asserts for a " ?width " by " ?height "  world." crlf)
  (bind ?x 1)
  (while (<= ?x ?width)
    (bind ?y 1)
    (while (<= ?y ?height)
      (if (> ?x 1) then (assert (adj  ?x ?y (- ?x 1) ?y)))
      (if (> ?y 1) then (assert (adj ?x ?y ?x (- ?y 1))))
      (if (< ?x ?width) then (assert (adj ?x ?y (+ ?x 1) ?y)))
      (if (< ?y ?height) then (assert (adj ?x ?y ?x (+ ?y 1))))
      (bind ?y (+ 1 ?y)))
    (bind ?x (+ ?x 1))))

(deffunction between (?x1 ?y1 ?x2 ?y2 ?x3 ?y3)
  ;; Returns TRUE if (X2,Y2) is between (X1,Y1) and (X3,Y3).  That is,
  ;; going from X1Y1 to X2Y2 will bring us closer to X3Y3.
  (and (or (and (<= ?x1 ?x2)(<= ?x2 ?x3))
           (and (<= ?x3 ?x2)(<= ?x2 ?x1)))
      (or (and (<= ?y1 ?y2)(<= ?y2 ?y3))
          (and (<= ?y3 ?y2)(<= ?y2 ?y1)))))

;; rules ====================================================================
(defrule in-the-beginning 
  (initial-fact)  
  => 
  (printout t "GENESIS..." crlf)
  (assert (task genesis)))

;; GENESIS rules  --------------------------------------------------------------
(defrule buildworld
  "This rule will call the buildworld function which will add the adj/4
    assertions for the current world"
  (task genesis) 
  (worldsize ?width ?height)
  =>
  (buildworld ?width ?height))

(defrule retract-nocaves 
  "This rule will retract adj/4 assertions added by buildworld when a
    matching nocave assertion is present"
  (task genesis) 
  (nocave (x ?x)(y ?y))
  ?adj <- (or (adj ?x2 ?y2 ?x ?y)(adj ?x ?y ?x2 ?y2))
  =>
  (retract ?adj))

(defrule buildworld
  "This rule will call the buildworld function which will add the adj/4
    assertions for the current world"
  (task genesis) 
  (worldsize ?width ?height)
  =>
  (buildworld ?width ?height))

(defrule put-hunter-in-caves
  "Assuming the hunter has no (X,Y) in the caves, find an exit
   and put him there."
  (task genesis)
  ?hunter <- (hunter (agent ?a)(x nil)(y nil))
  (exit (x ?x)(y ?y))
  =>
  (printout t ?a " enters the caves at (" ?x "," ?y ")." crlf)
  (modify ?hunter (x ?x)(y ?y)))

;; SIMULATE rules --------------------------------------------------------------
(defrule meet-the-wumpus
  "If a hunter and wumpus are in the same cave..."
  (task simulate)
  ?hunter <- (hunter (x ?x) (y ?y) (alive TRUE))
  (wumpus (x ?x) (y ?y) (alive TRUE))
  =>
  (printout t "Aaarrrggghhhhhh....munch...munch...munch" crlf)
  (modify ?hunter (alive FALSE))
  (halt))

(defrule fall-into-the-pit
  "If a hunter and pit are in the same cave..."
  (task simulate)
  ?hunter <- (hunter (x ?x) (y ?y) (alive TRUE))
  (pit (x ?x) (y ?y))
  =>
  (printout t "Aaarrrggghhhhhh....plop" crlf)
  (modify ?hunter (alive FALSE))
  (halt))

;; SENSE rules --------------------------------------------------------------
(defrule enter-new-cave
  "If we are in a cave for the first time, mark it as visited.
   This rule is only needed when the hunter wakes up in the exit cave"
  (task sense) 
  (hunter (agent ?agent) (x ?x) (y ?y))
  (not (cave (x ?x)(y ?y)))
  =>
  ;(printout t ?agent " enters (" ?x "," ?y ")." crlf) 
  (assert (cave (x ?x)(y ?y)(visited TRUE))))

(defrule enter-cave-for-first-time
  "If we are in a cave for the first time, mark it as visited"
  (task sense) 
  (hunter (agent ?agent) (x ?x) (y ?y))
  ?cave <- (cave (x ?x)(y ?y)(visited FALSE))
  =>
  ;(printout t ?agent " enters (" ?x "," ?y ")." crlf) 
  (modify ?cave (visited TRUE)))

(defrule notice-other-caves
  "If we've just entered a new cave, we notice the other adjacent caves."
  (task sense) 
  (hunter (agent ?agent) (x ?x)(y ?y))
  (adj ?x ?y ?x2 ?y2)
  (not (cave (x ?x2)(y ?y2)))
  => 
  (printout t ?agent " notices (" ?x2 "," ?y2 ") nearby." crlf) 
  (assert (cave (x ?x2)(y ?y2))))

(defrule sense-breeze
  "Sense a breeze if a pit is nearby"
  (task sense) 
  (hunter (agent ?agent) (x ?x) (y ?y))
  ?cave <- (cave(x ?x)(y ?y)(breeze UNKNOWN))
  (adj ?x ?y ?x2 ?y2)
  (pit (x ?x2) (y ?y2))
  =>
  (printout t ?agent " feels a breeze in (" ?x "," ?y ")." crlf) 
  (modify ?cave (breeze TRUE)))

(defrule sense-breeze-none
  "Sense a breeze if a pit is nearby"
  (declare  (salience -1))
  (task sense) 
  (hunter (agent ?agent) (x ?x) (y ?y))
  ?cave <- (cave(x ?x)(y ?y)(breeze UNKNOWN))
  =>
  (printout t ?agent " feels no breeze in (" ?x "," ?y ")." crlf) 
  (modify ?cave (breeze FALSE)))

(defrule sense-stench
  "Sense a stench if a living wumpus is nearby"
  (task sense) 
  (hunter (agent ?agent) (x ?x) (y ?y))
  ?cave <- (cave (x ?x)(y ?y)(stench UNKNOWN))
  (adj ?x ?y ?x2 ?y2)
  (wumpus (x ?x2) (y ?y2) (alive TRUE))
   =>
  (printout t ?agent " smells a stench." crlf) 
  (modify ?cave (stench TRUE)))

(defrule sense-stench-none
  "Sense a stench if a living wumpus is nearby"
  (declare (salience -1))
  (task sense) 
  (hunter  (agent ?agent)(x ?x) (y ?y))
  ?cave <- (cave (x ?x)(y ?y)(stench UNKNOWN))
  =>
  (printout t  ?agent " smells nothing." crlf) 
  (modify ?cave (stench FALSE)))

(defrule sense-glitter
  "Sense glitter if gold in this cave"
  (task sense) 
  (hunter  (agent ?agent) (x ?x) (y ?y))
  ?cave <- (cave (x ?x)(y ?y)(glitter UNKNOWN))
  (gold (x ?x) (y ?y) (amount ?n))
  (test (> ?n 0))
  =>
  (printout t   ?agent " sees glitter." crlf) 
  (modify ?cave (glitter TRUE)))

(defrule sense-glitter-none
  "Sense a breeze if gold in this cave"
  (task sense) 
  (hunter (agent ?a)(x ?x) (y ?y))
  ?cave <- (cave (x ?x)(y ?y)(glitter UNKNOWN))
  (not (gold (x ?x) (y ?y) (amount ?n&:(> ?n 0))))
  =>
  (printout t ?a " sees no glitter." crlf) 
  (modify ?cave (glitter FALSE)))

;; THINK rules --------------------------------------------------------------
(defrule evaluate-stench-none
  (task think) 
  (cave (x ?x)(y ?y)(stench FALSE))
  (adj ?x ?y ?x2 ?y2)
  ?f <- (cave (x ?x2)(y ?y2)(has-wumpus ~FALSE))
  =>
  (printout t "No stench in (" ?x "," ?y ") means no wumpus in (" ?x2 ","  ?y2 ")." crlf)
  (modify ?f (has-wumpus FALSE)))

(defrule evaluate-stench
  (task think) 
  (cave (x ?x)(y ?y)(stench TRUE))
  (adj ?x ?y ?x2 ?y2)
  ?f <- (cave (x ?x2)(y ?y2)(has-wumpus UNKNOWN))
  =>
  (printout t "With stench in (" ?x "," ?y "), maybe the wumpus is in (" ?x2  "," ?y2 ")." crlf)
  (modify ?f (has-wumpus MAYBE)))

(defrule evaluate-breeze-none
  (task think) 
  (cave (x ?x)(y ?y)(breeze FALSE))
  (adj ?x ?y ?x2 ?y2)
  ?f <- (cave (x ?x2)(y ?y2)(has-pit ~FALSE))
  =>
  (printout t "There's no breeze in (" ?x "," ?y ") so there's no pit  in (" ?x2  "," ?y2 ")." crlf)
  (modify ?f (has-pit FALSE)))

(defrule evaluate-breeze
  (task think) 
  (cave (x ?x)(y ?y)(breeze TRUE))
  ?f <- (cave (x ?x2)(y ?y2)(has-pit UNKNOWN))
  (adj ?x ?y ?x2 ?y2)
  =>
  (printout t "A breeze in (" ?x "," ?y "), so there may be a pit in (" ?x2  "," ?y2 ")." crlf)
  (modify ?f (has-pit MAYBE)))
  
(defrule evaluate-glitter 
  (task think) 
  (hunter (agent ?a)(x ?x)(y ?y))
  ?cave <- (cave (x ?x)(y ?y)(glitter TRUE)(has-gold ~TRUE))
  => 
  (printout t "Seeing glitter, " ?a " knows there is gold in (" ?x "," ?y ")." crlf)
  (modify ?cave (has-gold TRUE)))

(defrule evaluate-glitter-none 
  (task think) 
  (hunter (agent ?a)(x ?x)(y ?y))
  ?cave <- (cave (x ?x)(y ?y)(glitter FALSE)(has-gold ~FALSE))
  => 
  (printout t "Seeing no glitter, " ?a " knows there is no gold in (" ?x "," ?y ")." crlf)
  (modify ?cave (has-gold FALSE)))

(defrule safe-cave
  (task think) 
  ?f <- (cave (x ?x)(y ?y) (has-wumpus FALSE)(has-pit FALSE)(safe UNKNOWN))
  =>
  (printout t "With neither wumpus nor pit, (" ?x "," ?y ") is safe." crlf)
  (modify ?f (safe TRUE)))

(defrule safe-cave2
  (task think) 
  (hunter (agent ?agent) (x ?x)(y ?y)(alive TRUE))
   ?f <- (cave (x ?x)(y ?y)(safe UNKNOWN))
  =>
  (printout t "Since " ?agent " is in ("?x "," ?y ") and not dead, it must be safe." crlf)
  (modify ?f (safe TRUE)))

(defrule safe-cave3
 "safe => ~wumpus ^ ~pit"
  (task think) 
  (or ?f <- (cave (x ?x)(y ?y)(safe TRUE)(has-wumpus ~FALSE))
      ?f <- (cave (x ?x)(y ?y)(safe TRUE)(has-pit ~FALSE)))
  =>
  (printout t "(" ?x "," ?y ") is safe, so there's no pit or wumpus in it." crlf)
  (modify ?f (has-wumpus FALSE)(has-pit FALSE)))

;; setting desires ...
(defrule desire-to-leave-caves 
  (task think)
  (hunter (agent ?a)(x ?x)(y ?y)(gold ~0))
  (cave (x ?x)(y ?y)(has-exit TRUE))
  => 
  (printout t "Having found the gold, " ?a " want to leave the caves." crlf)
  (assert (desire (agent ?a)(strength ?*veryhigh*)(action leavecaves))))

(defrule add-desire-to-head-for-the-exit
  (task think) 
  (hunter (agent ?agent) (x ?x)(y ?y)(gold ~0))
  (cave (x ?x)(y ?y)(fromx ?fx)(fromy ?fy))
  (test (> ?fx 0))
  =>  
 (printout t ?agent " strongly wants to go to (" ?fx "," ?fy ")." crlf)
 (assert (desire (agent ?agent) (strength ?*veryhigh*) (action go)(x ?fx)(y ?fy))))

(defrule lust-for-gold
  (task think) 
  (hunter (agent ?a)(x ?x)(y ?y))
  (cave (x ?x)(y ?y)(has-gold TRUE))
  =>
  (printout t ?a " wants to pick up the gold in (" ?x "," ?y ")." crlf)
  (assert (desire (agent ?a)(strength ?*veryhigh*)(action pickupgold))))

(defrule retract-lesser-desire
  "If we have two desires for the same thing, remove the one with lesser strength"
 (task think) 
 (desire (agent ?agent)(strength ?s1)(action ?a)(x ?x)(y ?y))
 ?desire2 <- (desire (agent ?agent)(strength ?s2)(action ?a)(x ?x)(y ?y))
 (test (< ?s2 ?s1))
 =>
 (retract ?desire2))

(defrule add-desire-to-go-to-safe-adjacent-cave
 "go to an adjacent, safe, unvisited cave"
 (task think) 
 (hunter (agent ?agent)(x ?x)(y ?y))
 (adj ?x ?y ?x2 ?y2)
 (cave (x ?x2)(y ?y2)(visited FALSE)(safe TRUE))
 => 
 (printout t ?agent " strongly wants to go to (" ?x2 "," ?y2 ")." crlf)
 (assert (desire (agent ?agent) (strength ?*high*) (action go)(x ?x2)(y ?y2))))

(defrule add-desire-to-go-to-safe-distant-cave 
 "go to a non-adjacent, safe, unvisited cave"
 (task think) 
 (hunter (agent ?agent)(x ?x)(y ?y))
 (cave (x ?x2)(y ?y2)(visited FALSE)(safe TRUE))
 (not (adj ?x ?y ?x2 ?y2))
 => 
 (printout t ?agent " moderately wants to go to (" ?x2 "," ?y2 ")." crlf)
 (assert (desire (agent ?agent) (strength ?*medium*) (action go)(x ?x2)(y ?y2))))

(defrule add-desire-to-go-to-risky-adjacent-cave
 "go to an adjacent, risky, unvisited cave"
 (task think) 
 (hunter (agent ?agent)(x ?x)(y ?y))
 (cave (x ?x2)(y ?y2)(visited FALSE)(safe UNKNOWN))
 (adj ?x ?y ?x2 ?y2)
 => 
 (printout t ?agent " somewhat wants to go to (" ?x2 "," ?y2 ")." crlf)
 (assert (desire (agent ?agent) (strength ?*low*) (action go)(x ?x2)(y  ?y2))))

(defrule add-desire-to-go-to-risky-distant-cave
 "go to a distant, risky, unvisited cave"
 (task think) 
 (hunter (agent ?agent)(x ?x)(y ?y))
 (cave (x ?x2)(y ?y2)(visited FALSE)(safe UNKNOWN))
 (not (adj ?x ?y ?x2 ?y2))
 => 
 (printout t ?agent " somewhat wants to go to (" ?x2 "," ?y2 ")." crlf)
 (assert (desire (agent ?agent) (strength ?*verylow*) (action go)(x ?x2)(y  ?y2))))


;; PLAN rules  --------------------------------------------------------------
;; Planning our action is just simply picking the desire to realize
;; and asserting an appropriate goal.
(defrule choose-desire 
  "pick the best desire available for a given action. note that we
    will only promote one desire to be a goal at a time."
  (task plan)
  ?f <- (desire (strength ?s)(action ?act)(x ?x)(y ?y))
  (not (desire (strength ?s2&:(> ?s2 ?s))))
  (not (goal))
  => 
 (retract ?f)
 (assert (goal (action ?act) (x ?x)(y ?y))))

;; ACT rules  --------------------------------------------------------------
;; These rules find a goal and take actions to carry it out.
(defrule found-exit
  "If the hunter has gold and finds an exit, she leaves."
  (task act) 
  (hunter (agent ?agent) (x ?x)(y ?y)(gold ~0))
  (exit (x ?x)(y ?y))
  =>  
 (printout t ?agent " leaves the caves." crlf)
 (halt))

(defrule pickup-gold 
  "If we find the gold, pick it up"
  (task act)
  ?goal <- (goal (action pickupgold))
  ?f1 <- (hunter (agent ?a)(x ?x)(y ?y)(gold ?current))
  ?cave <- (cave (x ?x)(y ?y)(has-gold TRUE)) 
  ?f2 <- (gold (x ?x)(y ?y)(amount ?more))
  (test (> ?more 0))
  =>
  (printout t ?a " picks up " ?more " pieces of gold!" crlf)
  (retract ?goal)
  (modify ?f1 (gold (+ ?current ?more)))
  (modify ?cave (has-gold FALSE)(glitter FALSE))
  (modify ?f2 (amount 0))) 

(defrule go-to-adjacent-cave
  "If our desire is to goto XY and were are in an adjacent cell,
   do it and remove the desire"
  (task act)
  ?goal <- (goal (action go) (x ?x)(y ?y))
  ?hunter <-(hunter (agent ?agent) (x ?x2)(y ?y2))
  (adj ?x ?y ?x2 ?y2)
  ?target <- (cave (x ?x)(y ?y)(visited ?v))
  =>
  (printout t ?agent " goes to (" ?x "," ?y ")." crlf)
  (retract ?goal) 
  (modify ?hunter (x ?x)(y ?y))
  (if (not ?v) then (modify ?target (fromx ?x2)(fromy ?y2))))

(defrule move-toward-distant-cave
  "The hunter is in X1Y1 and intends to go to distant X3Y3.  Hunter
  goes to adjacent safe cave X2Y2 which is closer to X3Y3."
  (task act)
  ?hunter <-(hunter (agent ?agent) (x ?x1)(y ?y1))
  (goal (action go) (x ?x3)(y ?y3))
  (not (adj ?x1 ?y1 ?x3 ?y3))
  (cave (x ?x2)(y ?y2)(safe TRUE))
  (adj ?x1 ?y1 ?x2 ?y2)
  (test (between ?x1 ?y1 ?x2 ?y2 ?x3 ?y3))
  =>
  (printout t ?agent " goes to (" ?x2 "," ?y2 ") trying to get to (" ?x3 "," ?y3 ")." crlf)
  (modify ?hunter (x ?x2)(y ?y2)))

(defrule delete-desires
  "retracts any desire facts in the database" 
  (task act)
  (deletedesires)
  ?f <- (desire)
  => 
  (retract ?f))

(defrule delete-desires-end
  "retracts any desire facts in the database"
  (task act)
  (deletedesires)
  (not (desire))
  => 
  (retract (deletedesires)))

(defrule retract-satisfied-goal
  ;; this shouldn't happen, and is here for debugging.
  (task act)
  ?goal <- (goal (agent ?a) (action go)(x ?x)(y ?y))
  (hunter (agent ?a) (x ?x)(y ?y))
  =>
  (printout t "WARNING: " ?a " has a goal to go to (" ?x "," ?y ") and she is already here." crlf)
  (retract ?goal))

(defrule retract-satisfied-goal
  ;; this shouldn't happen, and is here for debugging.
  (declare (salience -1))
  (task act)
  ?goal <- (goal (agent ?a) (action ?act)(x ?x)(y ?y))
  =>
  (printout t "WARNING: unsatisfied goal: " ?act " " ?x " " ?y "."  crlf)
  (halt))

;; TASK SWITCHING rules -------------------------------------------------------
;; These rules cycle us through the various tasks.  Note that they all
;; have a very low salience, so that they will be run last.  Depending
;; on which is the current task, the rules just move us on to the
;; next.  we start in genesis, the move to a cycle of (simulate,
;; sense, think, plan, act).
(defrule genesis-to-simulate
  (declare  (salience -100))
  ?f <- (task genesis)
  =>
  (retract ?f)
  (printout t "SIMULATING..." crlf)
  (assert (task simulate)))

(defrule simulate-to-sense
  (declare  (salience -100))
  ?f <- (task simulate)
  =>
  (retract ?f)
  (printout t "SENSING..." crlf)
  (assert (task sense)))

(defrule sense-to-think
  (declare  (salience -100))
  ?f <- (task sense)
  =>
  (retract ?f)
  (printout t "THINKING..." crlf)
  (assert (task think)))

(defrule think-to-plan
  (declare  (salience -100))
  ?f <- (task think)
  =>
  (retract ?f)
  (printout t "PLANNING..." crlf)
  (assert (task plan)))

(defrule plan-to-act
  (declare  (salience -100))
  ?f <- (task plan)
  =>
  (retract ?f)
  (printout t "ACTING..." crlf)
  (assert (task act)))

(defrule act-to-simulate
  (declare  (salience -100))
  ?f <- (task act)
  =>
  (retract ?f)
  (printout t "SIMULATING..." crlf)
  (assert (task simulate)))
