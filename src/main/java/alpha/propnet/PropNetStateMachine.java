package alpha.propnet;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;


@SuppressWarnings("unused")
public class PropNetStateMachine extends StateMachine {
    /** The underlying proposition network  */
    private PropNet propNet;
    /** The topological ordering of the propositions */
    private List<Proposition> ordering;
    /** The player roles */
    private List<Role> roles;

    /**
     * Initializes the PropNetStateMachine. You should compute the topological
     * ordering here. Additionally you may compute the initial state here, at
     * your discretion.
     */
    @Override
    public void initialize(List<Gdl> description) {
        try {
            propNet = OptimizingPropNetFactory.create(description);
            /*
            System.out.println("Component size: " + propNet.getSize());
            System.out.println("Proposition size: " + propNet.getPropositions().size());
            System.out.println("Base Proposition size: " + propNet.getBasePropositions().size());
            System.out.println("Input Proposition size: " + propNet.getInputPropositions().size());
            System.out.println("Legal Proposition size: " + propNet.getLegalPropositions().size());
            System.out.println("Goal Proposition size: " + propNet.getGoalPropositions().size());
            for (Component c: propNet.getInitProposition().getOutputs()) {
            	//System.out.println("Init Proposition output: " + c.toString());
            	//System.out.println("Init Proposition output output: " + c.getSingleOutput().toString());
            	//System.out.println("Init Proposition output output: " + c.getSingleOutput().getSingleOutput().toString());
            }
            */
            roles = propNet.getRoles();
            ordering = getOrdering();
            //System.out.println("Ordering size: " + ordering.size());
            propNet.renderToFile("Yeah.dot");
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    private void markBases(MachineState state) {
    	//System.out.println("markBases called");
    	Map<GdlSentence, Proposition> basePropositions = propNet.getBasePropositions();
    	Set<GdlSentence> contents = state.getContents();
    	for (GdlSentence name : basePropositions.keySet()) {
    		if (contents.contains(name)) {
    			basePropositions.get(name).setValue(true);
    		} else {
    			basePropositions.get(name).setValue(false);
    		}
    	}
    }

    private void markActions(List<Move> moves) {
    	//System.out.println("markActions called");
    	Map<GdlSentence, Proposition> inputPropositions = propNet.getInputPropositions();
    	List<GdlSentence> does = toDoes(moves);
    	for (GdlSentence name : inputPropositions.keySet()) {
    		if (does.contains(name)) {
    			//System.out.println("setting " + name + " to true");

    			inputPropositions.get(name).setValue(true);
    		} else {
    			//System.out.println("setting " + name + " to false");

    			inputPropositions.get(name).setValue(false);
    		}
    	}
    }

    /**
     * Computes if the state is terminal. Should return the value
     * of the terminal proposition for the state.
     */
    @Override
    public boolean isTerminal(MachineState state) {
    	//System.out.println("isTerminal called");
    	//System.out.println(state);
        // TODO: Compute whether the MachineState is terminal.
    	//getInitialState();
    	markBases(state);
    	forward();
        return propNet.getTerminalProposition().getValue();
    }

    /**
     * Computes the goal for a role in the current state.
     * Should return the value of the goal proposition that
     * is true for that role. If there is not exactly one goal
     * proposition true for that role, then you should throw a
     * GoalDefinitionException because the goal is ill-defined.
     */
    @Override
    public int getGoal(MachineState state, Role role)
            throws GoalDefinitionException {
        // TODO: Compute the goal for role in state.
    	//System.out.println(state);
    	//getInitialState();
    	markBases(state);
    	forward();
    	Set<Proposition> goals = propNet.getGoalPropositions().get(role);
    	Proposition result = null;
    	for(Proposition prop: goals) {
    		if (prop.getValue() == true) {
    			if (result != null) throw new GoalDefinitionException(state, role);
    			else result = prop;
    		}
    	}
    	if (result == null) throw new GoalDefinitionException(state, role);
    	return getGoalValue(result);
    }

    /**
     * Returns the initial state. The initial state can be computed
     * by only setting the truth value of the INIT proposition to true,
     * and then computing the resulting state.
     */
    @Override
    public MachineState getInitialState() {
    	//System.out.println("getInitialState called");
        // TODO: Compute the initial state.
    	for (Proposition p : propNet.getBasePropositions().values()) p.setValue(false);
    	for (Proposition p : propNet.getInputPropositions().values()) p.setValue(false);
    	propNet.getInitProposition().setValue(true);
    	forward();
    	MachineState newstate = getStateFromBase();
    	propNet.getInitProposition().setValue(false);
    	return newstate;
    }

    /**
     * Computes all possible actions for role.
     */
    @Override
    public List<Move> findActions(Role role)
            throws MoveDefinitionException {
    	//System.out.println("findActions called");
        Map<Role, Set<Proposition>> map = propNet.getLegalPropositions();
        Map<Proposition, Proposition> legalToInput = propNet.getLegalInputMap();
        Set<Proposition> actions = map.get(role);
        Set<GdlSentence> results = new HashSet<GdlSentence>();
        for (Proposition prop: actions) {
        	results.add(legalToInput.get(prop).getName());
        }

        List<Move> moves = new ArrayList<Move>();
        for (GdlSentence result : results)
        {
            moves.add(new Move(result.get(1)));
        }

        //System.out.println("haha");
        //System.out.println(moves);

        return moves;
    }

    /**
     * Computes the legal moves for role in state.
     */
    @Override
    public List<Move> getLegalMoves(MachineState state, Role role)
            throws MoveDefinitionException {
        // TODO: Compute legal moves
    	//System.out.println("getLegalMoves called");
    	//System.out.println(state);
    	//getInitialState();
    	markBases(state);
    	forward();
    	Map<Role, Set<Proposition>> legalPropositions = propNet.getLegalPropositions();
        Set<Proposition> ps = legalPropositions.get(role);
        //System.out.println("ps : " + ps);
    	Map<Proposition, Proposition> legalToInput = propNet.getLegalInputMap();

        List<Move> moves = new ArrayList<Move> ();
        for (Proposition p : ps) {
        	//System.out.println("p is " + p);
        	//System.out.println(p.getValue());
        	if(p.getValue()) {
        		//System.out.println("adding move ");
        		moves.add(getMoveFromProposition(legalToInput.get(p)));
        	}
        }

        //System.out.println("weightout forward");
        //System.out.println(moves);

        return moves;
    }


    public void propMark() {
    	for (Proposition p : propNet.getBasePropositions().values()) {
        	p.setValue(p.getSingleInput().getValue());
        }
    }

    /**
     * Computes the next state given state and the list of moves.
     */
    @Override
    public MachineState getNextState(MachineState state, List<Move> moves)
            throws TransitionDefinitionException {
        // TODO: Compute the next state.
    	//getInitialState();
    	//System.out.println("getNextState called");
    	//System.out.println(state);
    	markBases(state);
    	markActions(moves);
    	forward();
    	//propMark();
    	return getStateFromBase();
	}

    private void forward() {
    	//System.out.println("forward called");
    	for (Proposition p : ordering) {
    		p.setValue(p.getSingleInput().getValue());
    	}
    }

    /**
     * This should compute the topological ordering of propositions.
     * Each component is either a proposition, logical gate, or transition.
     * Logical gates and transitions only have propositions as inputs.
     *
     * The base propositions and input propositions should always be exempt
     * from this ordering.
     *
     * The base propositions values are set from the MachineState that
     * operations are performed on and the input propositions are set from
     * the Moves that operations are performed on as well (if any).
     *
     * @return The order in which the truth values of propositions need to be set.
     */
    public List<Proposition> getOrdering() {
    	//System.out.println("getOrdering called");
    	// List to contain the topological ordering.
        List<Proposition> order = new LinkedList<Proposition>();

        // All of the components in the PropNet
        List<Component> components = new ArrayList<Component>(propNet.getComponents());

        // All of the propositions in the PropNet.
        List<Proposition> propositions = new ArrayList<Proposition>(propNet.getPropositions());

        List<Component> operations = components;
        operations.removeAll(propositions);
        //System.out.println("Number of Operations: " + operations.size());
        Set<Proposition> combined = new HashSet<Proposition>(propNet.getBasePropositions().values());
        combined.addAll(propNet.getInputPropositions().values());
        combined.add(propNet.getInitProposition());
        /*for(Set<Proposition> props : propNet.getLegalPropositions().values()) {
        	 combined.addAll(props);
        }*/
        //System.out.println("Number of Base and Input propositions: " + combined.size());
        int num_proposition = 0;
        int num_connectives = 0;
        List<Component> bruh = new LinkedList<Component> (combined);
        for(Component c: components) {
        	if(c.getInputs().size() == 0 && !combined.contains(c))
        		bruh.add(c);
        }
        while(bruh.size()!=0) {
        	Component p = bruh.remove(0);
        	p.setVisited();
        	if (p instanceof Proposition && !combined.contains(p)) order.add((Proposition)p);
        	for(Component out : p.getOutputs()) {
        		if (!(out instanceof Transition) && out.canAdd()) bruh.add(out);
        	}
        }
        return order;

        /*List<Proposition> new_order = new LinkedList<Proposition>();
        for (int i = order.size() -1; i >= 0; i-- ) {
        	if(new_order.contains(order.get(i))) continue;
        	new_order.add(0, order.get(i));
        }
        Set<Proposition> set_order = new HashSet<Proposition>(order);
        System.out.println("Set size: " + set_order.size());
        System.out.println("Number of propositions in order" + new_order.size());
        return new_order;*/
    }



    public List<Proposition> getOrdering1()
    {
        // List to contain the topological ordering.
        List<Proposition> order = new LinkedList<Proposition>();

        // All of the components in the PropNet
        List<Component> components = new ArrayList<Component>(propNet.getComponents());

        // All of the propositions in the PropNet.
        List<Proposition> propositions = new ArrayList<Proposition>(propNet.getPropositions());

        //System.out.println("Number of propositions: " + propositions.size());
        // TODO: Compute the topological ordering.
        List<Component> operations = components;
        operations.removeAll(propositions);
        //System.out.println("Number of Operations: " + operations.size());
        Set<Proposition> combined = new HashSet<Proposition>(propNet.getBasePropositions().values());
        combined.addAll(propNet.getInputPropositions().values());
        //System.out.println("Number of Base and Input propositions: " + combined.size());
        int num_proposition = 0;
        int num_connectives = 0;
        List<Component> bruh = new LinkedList<Component> ();
        for (Component op : operations) {
        	if (combined.containsAll(op.getInputs())) {
        		bruh.add(op);
        		num_connectives ++;
        		//System.out.println("bruh adding " + op.getClass().getName());
        	}
        }
        while (bruh.size() != 0) {
        	Component op = bruh.remove(0);
        	for (Component out : op.getOutputs()) {
        		if (!combined.contains(out)) {
        			if (!(out instanceof Proposition)) {
        				bruh.add(out);
        				num_connectives ++;
        				continue;
        			}
        			//System.out.println("duiying de op shi :" + op.getClass().getName());
        			//System.out.println("out is ... dadadada " + out.getClass().getName());
        			//System.out.println(!(op instanceof Proposition));
        			//System.out.println(out instanceof Proposition);
        			order.add((Proposition) out);
        			bruh.addAll(out.getOutputs());
        			num_connectives += out.getOutputs().size();
        		}
        	}
        }

        List<Proposition> new_order = new LinkedList<Proposition>();
        for (int i = order.size() -1; i >= 0; i-- ) {
        	if(new_order.contains(order.get(i))) continue;
        	new_order.add(0, order.get(i));
        }
        Set<Proposition> set_order = new HashSet<Proposition>(order);
        //System.out.println("Set size: " + set_order.size());
        //System.out.println("Number of propositions in order" + new_order.size());
        return new_order;
    }

    /* Already implemented for you */
    @Override
    public List<Role> getRoles() {
        return roles;
    }

    /* Helper methods */

    /**
     * The Input propositions are indexed by (does ?player ?action).
     *
     * This translates a list of Moves (backed by a sentence that is simply ?action)
     * into GdlSentences that can be used to get Propositions from inputPropositions.
     * and accordingly set their values etc.  This is a naive implementation when coupled with
     * setting input values, feel free to change this for a more efficient implementation.
     *
     * @param moves
     * @return
     */
    private List<GdlSentence> toDoes(List<Move> moves)
    {
        List<GdlSentence> doeses = new ArrayList<GdlSentence>(moves.size());
        Map<Role, Integer> roleIndices = getRoleIndices();

        for (int i = 0; i < roles.size(); i++)
        {
            int index = roleIndices.get(roles.get(i));
            doeses.add(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)));
        }
        return doeses;
    }

    /**
     * Takes in a Legal Proposition and returns the appropriate corresponding Move
     * @param p
     * @return a PropNetMove
     */
    public static Move getMoveFromProposition(Proposition p)
    {
        return new Move(p.getName().get(1));
    }

    /**
     * Helper method for parsing the value of a goal proposition
     * @param goalProposition
     * @return the integer value of the goal proposition
     */
    private int getGoalValue(Proposition goalProposition)
    {
        GdlRelation relation = (GdlRelation) goalProposition.getName();
        GdlConstant constant = (GdlConstant) relation.get(1);
        return Integer.parseInt(constant.toString());
    }

    /**
     * A Naive implementation that computes a PropNetMachineState
     * from the true BasePropositions.  This is correct but slower than more advanced implementations
     * You need not use this method!
     * @return PropNetMachineState
     */
    public MachineState getStateFromBase()
    {
        Set<GdlSentence> contents = new HashSet<GdlSentence>();
        for (Proposition p : propNet.getBasePropositions().values())
        {
        	p.setValue(p.getSingleInput().getValue());
            if (p.getValue())
            {
                contents.add(p.getName());
            }

        }
        return new MachineState(contents);
    }
}