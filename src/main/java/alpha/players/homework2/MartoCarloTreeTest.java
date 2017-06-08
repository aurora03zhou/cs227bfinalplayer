package alpha.players.homework2;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.ggp.base.apps.player.detail.DetailPanel;
import org.ggp.base.apps.player.detail.SimpleDetailPanel;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

import alpha.propnet.PropNetStateMachine;

public class MartoCarloTreeTest extends StateMachineGamer {

	public static final int PROBE = 10;
	public static final int FRACTION_SELECT = 6;
	public static final int FRACTION_MC = 8;
	public static final int FRACTION_DC = 8;
	public static final double C = 5;
	private long s = 0;
	private long tout = 0;
	private Node root;

	private class Node {
		int visited = 0;
		double utility = 0;
		boolean max;
		boolean full;
		Node parent;
		Move move;
		List<Move> moves;
		List<List<Move>> jointmoves;
		MachineState state;
		ArrayList <Node> children;

		private Node (MachineState state, Node parent, boolean max, List<List<Move>> jointmoves) throws MoveDefinitionException{
			this.state = state;
			this.parent = parent;
			this.max = max;
			if (max) this.moves = new ArrayList<Move>(getStateMachine().getLegalMoves(state, getRole()));
			this.full = false;
			this.jointmoves = jointmoves;
			this.children = new ArrayList <Node>();
		}

		void addChild(Node child) {
			children.add(child);
		}

		void setMove(Move move) {
			if (max) System.out.println("This is a max node, stop setting move.");
			this.move = move;
		}

		Move getMove() {
			if (!max) System.out.println("This is a min node, fatal error.");
			Move move = moves.remove(new Random().nextInt(moves.size()));
			return move;
		}

		List<Move> getJointMove() {
			if (max) System.out.println("This is a max node, fatal error.");
			List<Move> jointmove = jointmoves.remove(new Random().nextInt(jointmoves.size()));
			if (jointmoves.isEmpty()) {
				full = true;
				if (parent.moves.isEmpty()) {
					parent.full = true;
				}
			}
			return jointmove;
		}
	}

	@Override
	public DetailPanel getDetailPanel() {
		return new SimpleDetailPanel();
	}

	@Override
	public StateMachine getInitialStateMachine() {
		// TODO Auto-generated method stub
		return new CachedStateMachine(new PropNetStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		root = new Node(getCurrentState(), null, true, null);
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		List<Move> Moves = machine.getLegalMoves(getCurrentState(), getRole());

		long start = System.currentTimeMillis();
		s = start;
		tout = timeout;
		long finishBy = timeout - (timeout - start)/FRACTION_SELECT;
		Move result = machine.getRandomMove(getCurrentState(), getRole());
		if (Moves.size() == 1) return result;

		boolean singleplayer = (machine.getRoles().size() == 1);
/*
		if (singleplayer) {
			boolean found = false;
			for (Node maxnode : root.children) {
				if (maxnode.state.equals(getCurrentState())) {
					root = maxnode;
					root.parent = null;
					found = true;
					break;
				}
				if (found) break;
			}
			if (!found) root = new Node(getCurrentState(), null, true, null);

			// Select Move
			while(System.currentTimeMillis() < finishBy) {
				System.out.println("Starting, Time left: " + (tout - System.currentTimeMillis()));
				//Node node = selectSingle(root);
				//Node newnode = expandSingle(node);
				System.out.println("New state is max: " + newnode.max);
				double score = montecarlo(newnode);
				backpropagate(node, score);
			}

			double maxscore = 0;
			for (Node maxnode : root.children) {
				double score = maxnode.utility*1.0/maxnode.visited;
				if (score > maxscore) {
					maxscore = score;
					result = maxnode.move;
				}
			}
		}
*/
		// Move root
		boolean found = false;
		for (Node minnode : root.children) {
			for (Node maxnode : minnode.children) {
				if (maxnode.state.equals(getCurrentState())) {
					root = maxnode;
					root.parent = null;
					found = true;
					break;
				}
			}
			if (found) break;
		}
		if (!found) root = new Node(getCurrentState(), null, true, null);

		// Select Move
		while(System.currentTimeMillis() < finishBy) {
			//System.out.println("Starting, Time left: " + (tout - System.currentTimeMillis()));
			Node node = select(root);
			Node newnode = expand(node);
			//System.out.println("New state is max: " + newnode.max);
			double score = montecarlo(newnode);
			backpropagate(newnode, score);
		}

		double maxscore = 0;
		for (Node minnode : root.children) {
			double score = minnode.utility*1.0/minnode.visited;
			if (score > maxscore) {
				maxscore = score;
				result = minnode.move;
			}
		}

		return result;
	}

	// not full as usual full
	private Node select(Node node) {
		//System.out.println("Selecting, Time left: " + (tout - System.currentTimeMillis()));

		if (!node.full) {
			if (!node.max) System.out.println("Caution! Selecting a not full min node somehow! Parent maxnode should not be full!");
			return node;
		}
		Node minresult = node.children.get(0);
		double maxValue = selectFn(minresult);
		for (Node minnode : node.children) {
			double selectValue = selectFn(minnode);
			if (selectValue > maxValue) {
				maxValue = selectValue;
				minresult = minnode;
			}
		}

		Node maxresult = minresult.children.get(0);
		maxValue = selectFn(maxresult);
		for (Node maxnode : minresult.children) {
			if (getStateMachine().isTerminal(maxnode.state)) continue;
			double selectValue = selectFn(maxnode);
			if (selectValue > maxValue) {
				maxValue = selectValue;
				maxresult = maxnode;
			}
		}
		return select(maxresult);
	}

	private double selectFn(Node node){
		double result;
		if (node.max) result = -node.utility*1.0/node.visited + C*Math.sqrt(Math.log(node.parent.visited)/node.visited);
		else result = node.utility*1.0/node.visited + C*Math.sqrt(Math.log(node.parent.visited)/node.visited);
		return result;
	}

	private Node expand (Node node) throws MoveDefinitionException,TransitionDefinitionException{
		//System.out.println("Expanding, Time left: " + (tout - System.currentTimeMillis()));

		StateMachine machine = getStateMachine();
		if (machine.isTerminal(node.state)) return node;
		Node newNode = null;
		boolean minfull = true;
		for (Node minnode : node.children) {
			if(!minnode.full) {
				MachineState state = machine.getNextState(minnode.state, minnode.getJointMove());
				Node child = new Node(state, minnode, true, null);
				newNode = child;
				minnode.addChild(child);
				minfull = false;
				break;
			}
		}
		if (minfull) {
			// expand a minnode
			Move move = node.getMove();
			List<List<Move>> jointmoves = new ArrayList<List<Move>>(machine.getLegalJointMoves(node.state, getRole(), move));
			Node minnode = new Node(node.state, node, false, jointmoves);
			minnode.setMove(move);
			node.addChild(minnode);
			// and expand a maxnode
			MachineState state = machine.getNextState(minnode.state, minnode.getJointMove());
			Node child = new Node(state, minnode, true, null);
			newNode = child;
			minnode.addChild(child);
		}
		return newNode;
	}

	private double montecarlo(Node node) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		//System.out.println("Montecarloing, Time left: " + (tout - System.currentTimeMillis()));

		double total = 0;
		//System.out.println(node.state);
		//System.out.println(getStateMachine().getGoal(node.state, getRole()));
		for (int i = 0; i < PROBE; i++) {
			total += depthcharge(getRole(), node.state);
			if(System.currentTimeMillis() > tout - (tout - s) / FRACTION_MC) return total/(i+1);
		}
		return total/PROBE;
	}

	private double depthcharge(Role role, MachineState state) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		//System.out.println("Depthcharing, Time left: " + (tout - System.currentTimeMillis()));
		StateMachine theMachine = getStateMachine();
		//System.out.println("state is :" + state.toString());
		//MachineState currState = theMachine.performDepthCharge(state, null);
		MachineState currState = state;

		while (!theMachine.isTerminal(currState)) {
			currState = theMachine.getRandomNextState(currState);
		}

		return theMachine.getGoal(currState, role);
	}

	private void backpropagate (Node node,double score) {
		node.visited += 1;
		node.utility += score;
		if (node.parent != null) {
			backpropagate(node.parent, score);
		}
	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "A Good MCTS";
	}

}
