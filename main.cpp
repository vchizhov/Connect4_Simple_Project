#include "tigr.h"    //lightweight 2d graphics
#include <vector>    //for storing the successors of a given GameState
#include <bitset>    //used to represent the board in a minimum memory pool
#include <array>     //array duh
#include <math.h>    //misc
#include <algorithm> //std::sort
#include <sstream>   //ostringstream - uased to convert int to string
#include <thread>    //for multithreading


typedef signed char cell;
//10x10 board
const int c_board_width = 10;
const int c_board_height = 10;
//4 in a row/column/diagonal/anti-diagonal win condition
const int c_number_of_stones = 4;
//number of threads
const int c_num_threads = 8;

//a successors trim factor
const int c_trim = 5;
//maximum depth
const int c_depth = 5;
//min/max value for alphabeta negamax
const int extremePoints = 5;
//screen width and height
const int width = 800;
const int height = 800;

//the board I used to use before bitset
class board
{
private:
	cell* arr;
	

public:
	board()
	{
		arr = new cell[c_board_width*c_board_height];
		memset(arr, 0, sizeof(cell) * c_board_height * c_board_width);
	}

	board(board& mv) = delete;

	board(const board& other)
	{
		arr = new cell[c_board_width*c_board_height];
		memcpy(arr, other.arr, c_board_height*c_board_width);
	}

	board& operator=(const board& other)
	{
		memcpy(arr, other.arr, c_board_height*c_board_width);
		return *this;
	}

	~board()
	{
		delete[] arr;
	}

	const cell& operator()(const unsigned char x, const unsigned char y) const
	{
		return arr[x*c_board_height + y];
	}

	cell& operator()(const unsigned char x, const unsigned char y)
	{
		return arr[x*c_board_height + y];
	}
};

//enumeration of possible cell values
enum board_cell
{
	CELL_EMPTY = 0,
	CELL_P1 = 1,
	CELL_P2 = 2,
	CELL_UNDEFINED = 3
};

//the bitboard used to represent the board
class bitboard
{
private:
	std::bitset<2 * c_board_width*c_board_height> arr;

public:
	void set(int x, int y, board_cell val)
	{
		switch (val)
		{
		case CELL_EMPTY:
			arr.set(2 * (x*c_board_height + y), false);
			arr.set(2 * (x*c_board_height + y) + 1, false);
			break;
		case CELL_P1:
			arr.set(2 * (x*c_board_height + y), true);
			arr.set(2 * (x*c_board_height + y) + 1, false);
			break;
		case CELL_P2:
			arr.set(2 * (x*c_board_height + y), false);
			arr.set(2 * (x*c_board_height + y) + 1, true);
			break;
		case CELL_UNDEFINED:
			arr.set(2 * (x*c_board_height + y), true);
			arr.set(2 * (x*c_board_height + y) + 1, true);
			break;
		}
	}

	board_cell get(int x, int y) const
	{
		switch (arr.test(2 * (x*c_board_height + y)))
		{
		case false:
			switch (arr.test(2 * (x*c_board_height + y) + 1))
			{
			case false:
				return CELL_EMPTY;
				break;
			case true:
				return CELL_P2;
				break;
			}
			break;
		case true:
			return CELL_P1;
			break;
		}
	}
};

//a structure used to hold the output of a thread
struct thread_info
{
	int x, y, value;
	thread_info() : x(0), y(0), value(0) {}
	thread_info(int x, int y, int value) : x(x), y(y), value(value) {}
	//for sort
	bool operator<(const thread_info& other) const
	{
		return value > other.value;
	}
};

//main logical structure representing the game state
class GameState
{
private:
	//holds the current game board
	bitboard game_board;
	//the last move (x,y), current player's turn and the points(is the heuristic actually)
	int lastMoveX, lastMoveY;
	int current_player;
	int points;

	//a psuedo-heuristic for ordering
	int calcSurround() const
	{
		int arr_x[] = { -1,-1,-1, 0,1,1,1,0 };
		int arr_y[] = { -1, 0, 1, 1, 1, 0, -1, -1 };
		int acc = 0;
		for (int i = 0; i < 8; ++i)
		{
			if (-1 < lastMoveX + arr_x[i] && lastMoveX + arr_x[i] < c_board_width &&
				-1 < lastMoveY + arr_y[i] && lastMoveY + arr_y[i] < c_board_height &&
				game_board.get(lastMoveX + arr_x[i], lastMoveY + arr_y[i]) != CELL_EMPTY)
			{
				++acc;
			}
		}
		return acc;
	}

	//a comparator function used in std::sort for order_successors
	static bool compare(const GameState& a, const GameState& b)
	{
		return a.calcSurround() > b.calcSurround();
	}


	//heuristic function
	int check_outcome(const bitboard& current_board, int x, int y, board_cell player) const
	{
		int outcome = 2 * static_cast<int>(player) - 3;
		int sum = 1;
		//int outc = 0;
		//check horizontally
		int t = x - 1;
		while (t > -1 && sum < c_number_of_stones && current_board.get(t, y) == player)
		{
			sum++;
			t -= 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;

		t = x + 1;
		while (t < c_board_width && sum < c_number_of_stones && current_board.get(t, y) == player)
		{
			sum++;
			t += 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;// ++outc;

		//vertical
		sum = 1;
		t = y - 1;
		while (t > -1 && sum < c_number_of_stones && current_board.get(x, t) == player)
		{
			sum++;
			t -= 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;

		t = y + 1;
		while (t < c_board_height && sum < c_number_of_stones && current_board.get(x, t) == player)
		{
			sum++;
			t += 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;

		//main diagonal
		sum = 1;
		t = 1;
		while (x - t > -1 && y - t>-1 && sum < c_number_of_stones && current_board.get(x - t, y - t) == player)
		{
			sum++;
			t += 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;

		t = 1;
		while (x + t < c_board_width && y + t<c_board_height && sum < c_number_of_stones && current_board.get(x + t, y + t) == player)
		{
			sum++;
			t += 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;

		//secondary diagonal
		sum = 1;
		t = 1;
		while (x + t<c_board_width && y - t>-1 && sum < c_number_of_stones && current_board.get(x + t, y - t) == player)
		{
			sum++;
			t += 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;

		t = 1;
		while (x - t > -1 && y + t<c_board_height && sum < c_number_of_stones && current_board.get(x - t, y + t) == player)
		{
			sum++;
			t += 1;
		}
		if (sum >= c_number_of_stones)
			return outcome;

		return 0;
	}

	//generates the possible moves from this game state, outputs them in a vector
	void generate_successors(std::vector<GameState>& output) const
	{
		GameState temp(*this);
		for (int i = 0; i < c_board_width; ++i)
		{
			for (int j = 0; j < c_board_height; ++j)
			{
				if (game_board.get(i, j) == CELL_EMPTY)
				{
					//next player
					temp.current_player = 1 - temp.current_player;
					//heuristic function
					temp.points = check_outcome(game_board, i, j, static_cast<board_cell>(temp.current_player + 1));
					//init board
					temp.game_board.set(i, j, static_cast<board_cell>(temp.current_player + 1));
					temp.lastMoveX = i;
					temp.lastMoveY = j;
					output.push_back(temp);
					//undor temp changes
					temp.game_board.set(i, j, CELL_EMPTY);
					temp.points = points;
					temp.lastMoveX = lastMoveX;
					temp.lastMoveY = lastMoveY;
					temp.current_player = current_player;
					break;
				}
			}
		}
	}

	//ordering of the successoras and trimming
	void order_successors(std::vector<GameState>& output) const
	{
		std::sort(output.begin(), output.end(), compare);
		/*if (output.size() > c_trim)
			output.resize(c_trim);*/
	}

	//the main logic - Monte Carlo tree is better though
	int negamax(const GameState& state, int depth, int alpha, int beta, int color)
	{
		//depth end reached? or we actually hit a win/lose condition?
		if (depth == 0 || state.points != 0) 
		{

			return color*state.points;
		}

		//get successors and optimize the ordering/trim maybe too
		std::vector<GameState> childStates;
		state.generate_successors(childStates);
		state.order_successors(childStates);

		//no possible moves - then it's a terminal state
		if (childStates.empty())
		{
			return color*state.points;
		}
		int bestValue = -extremePoints;
		int v;
		for (GameState& child : childStates)
		{
			v = -negamax(child, depth - 1, -beta, -alpha, -color);
			bestValue = std::max(bestValue, v);
			alpha = std::max(alpha, v);
			if (alpha >= beta)
				break;
		}
		return bestValue;
	}

	//a thread program used in makeStep
	void threaded(const std::vector<GameState>& input, int start_index, int end_index, int depth, thread_info& out_info)
	{
		auto iter = input.begin();
		std::advance(iter, start_index);
		auto iter2 = input.begin();
		std::advance(iter2, end_index);
		int bestValue = -extremePoints;
		int v = 0;
		for (;iter!=iter2; ++iter)
		{
			v = -negamax(*iter, depth - 1, -extremePoints, extremePoints, -1);
			if (bestValue < v)
			{
				bestValue = v;
				out_info.x = iter->lastMoveX;
				out_info.y = iter->lastMoveY;
			}
		}
		out_info.value = bestValue;
	}
public:


	GameState()
	{
		points = 0;
		current_player = 0;
		lastMoveX = 0;
		lastMoveY = 0;
	}

	GameState(const GameState& parent)
		: game_board(parent.game_board), current_player(parent.current_player), points(parent.points), lastMoveX(parent.lastMoveX), lastMoveY(parent.lastMoveY)
	{

	}

	//player "player" puts a block on the current board at (x,y)
	void putBlock(int x, int y, int player)
	{
		points = check_outcome(game_board, x, y, static_cast<board_cell>(player + 1));
		game_board.set(x, y, static_cast<board_cell>(player + 1));
		lastMoveX = x;
		lastMoveY = y;
	}
	//the method making the decision for the AI step
	bool makeStep(int& x, int& y, int depth, int& belief)
	{
		std::vector<GameState> childStates;
		generate_successors(childStates);
		order_successors(childStates);
		if (childStates.empty())
			return false;
		//variables for the distribution of work to the threads
		int num_threads = 0;
		int thread_delta;
		int thread_rem;
		if (c_num_threads <= childStates.size())
		{
			num_threads = c_num_threads;
			thread_delta = childStates.size() / c_num_threads;
			thread_rem = childStates.size() % c_num_threads;
		}
		else
		{
			num_threads = childStates.size();
			thread_delta = 1;
			thread_rem = 0;
		}

		int bestValue = -extremePoints;
		int v = 0;
		int dp = depth;
		do
		{
			std::vector<std::thread> threads_array;
			threads_array.reserve(num_threads);
			//we'll be waiting for c++14 http://stackoverflow.com/questions/20857577/variable-length-stdarray-like
			std::array<thread_info, c_num_threads> threads_output;//the bug was from this being bigger than it needed to be
			//thread 0 starts first, that's why it gets the remainder too (it finishes before the other threads usually)
			threads_array.push_back(std::thread(&GameState::threaded, this, std::ref(childStates), 0, thread_delta + thread_rem, dp, std::ref(threads_output[0])));
			for (int i = 1; i < c_num_threads; ++i)//bad - should be num_threads
			{
				threads_array.push_back(std::thread(&GameState::threaded, this, std::ref(childStates), thread_rem + thread_delta*i, (i+1)*thread_delta + thread_rem, dp, std::ref(threads_output[i])));
			}
			//wait till all threads finish their job
			//we expect thread 0 to finish first

			for (int i = 0; i < c_num_threads; ++i)
			{
				threads_array[i].join();
			}
			//find the best value
			/*std::sort(threads_output.begin(), threads_output.end());*/
			//set
			for (int i =0;i<num_threads; ++i)
			{
				v = threads_output[i].value;
				if (bestValue < v)
				{
					bestValue = v;
					x = threads_output[i].x;
					y = threads_output[i].y;
				}
			}
			/*bestValue = threads_output[0].value;
			x = threads_output[0].x;
			y = threads_output[0].y;*/
			/*for (GameState& child : childStates)
			{
				v = -negamax(child, dp - 1, -extremePoints, extremePoints, -1);
				if (bestValue < v)
				{
					bestValue = v;
					x = child.lastMoveX;
					y = child.lastMoveY;
				}
			}*/
			if (dp == depth)
			{
				belief = bestValue;
			}
			--dp;
		} while (bestValue == -1 || dp > 1);

		putBlock(x, y, 1);
		return true;
	}

	int getLastMoveX() const
	{
		return lastMoveX;
	}

	int getLastMoveY() const
	{
		return lastMoveY;
	}

	int firstEmptyColumn(int x) const
	{
		int y = 0;
		while (y < c_board_height && game_board.get(x, y) != CELL_EMPTY)
		{
			++y;
		}
		return y;
	}

	int getPoints() const
	{
		return points;
	}
};

//a helper structure used for the graphics part
struct point
{
	int x, y;

	point(int x, int y) : x(x), y(y) {}
};

//the structure representing the board graphically
class GraphicsBoard
{
private:

	const int x, y, w, h;
	Tigr* board;
	TPixel gridCol, p1, p2;
public:

	GraphicsBoard(int x, int y, int w, int h, TPixel gridCol, TPixel p1, TPixel p2)
		:x(x),y(y), w(w), h(h), gridCol(gridCol), p1(p1), p2(p2)
	{
		board = tigrBitmap(w, h);
		tigrClear(board, tigrRGB(255, 255, 255));
		tigrRect(board, 0, 0, w, h, gridCol);
		int dx = w / c_board_width;
		int dy = h / c_board_height;
		for (int i = 0; i <= w; i += dx)
		{
			tigrLine(board, i, 0, i, h,gridCol);
		}
		for (int j = 0; j <= w; j += dy)
		{
			tigrLine(board, 0, j, w, j, gridCol);
		}
	}

	void addP1(int x, int y)
	{
		int dx = w / c_board_width;
		int dy = h / c_board_height;
		tigrFill(board, x*dx+1, (c_board_height-1-y)*dy+1, dx-1, dy-1, p1);
	}

	void addP2(int x, int y)
	{
		int dx = w / c_board_width;
		int dy = h / c_board_height;
		tigrFill(board, x*dx + 1, (c_board_height - 1 - y)*dy + 1, dx - 1, dy - 1, p2);
	}

	void draw(Tigr* bmp)
	{
		tigrBlit(bmp, board, x, y, 0, 0, w, h);
	}
	//convert from screen coordinates to grid coordinates
	void convertXY(int& x, int& y)
	{
		int dx = w / c_board_width;
		int dy = h / c_board_height;
		x = (x - this->x) / dx;
		y = (y - this->y) / dy;
	}
};



int main(int argc, char *argv[])
{
	//create teh main game state
	GameState game;
	//create the window and calculate xy margins
	Tigr *screen = tigrWindow(width, height, "ConnectFour", 0);
	int margin_x = width / 10;
	int margin_y = height / 10;
	//create the board
	GraphicsBoard board(margin_x, margin_y, width - 2 * margin_x, height - 2 * margin_y, tigrRGB(0, 0, 0), tigrRGB(255, 0, 0), tigrRGB(0, 255, 0));
	//win condition achieved?
	int win = 0;
	//will the AI lose if you play optimally the next few turns?
	int belief = 0;
	std::ostringstream blf;
	blf << "If you play optimally: " << belief;
	//a string stream for converting int to string
	std::ostringstream out;

	//if AI is first:
	game.putBlock(4, 0, 1);
	board.addP2(4, 0);

	//main loop
	while (!tigrClosed(screen) && !tigrKeyDown(screen, TK_ESCAPE))
	{
		tigrClear(screen, tigrRGB(255,255,255));

		int x, y, b;
		tigrMouse(screen, &x, &y, &b);
		board.convertXY(x, y);
		if (tigrKeyDown(screen, TK_SPACE) && 0<=x && x<c_board_width && (y = game.firstEmptyColumn(x))<c_board_height)
		{

			//player:
			//visually
			board.addP1(x, y);
			//logically
			game.putBlock(x, y, 0);
			if (game.getPoints() != 0)
			{
				win = 1;
				out << "Player " <<win << " wins!";
				break;
			}
			//AI:
			if (!game.makeStep(x, y, c_depth, belief))
			{
				blf.str("");
				blf << "If you play optimally: " << belief;
				out << "It's a draw!";
				win = -1;
				break;
			}
			else
			{
				blf.str("");
				blf << "If you play optimally: " << belief;
				
			}
			board.addP2(x,y);
			if (game.getPoints() != 0)
			{
				win = 2;
				out << "Player " << win << " wins!";
				break;
			}
		}
		

		board.draw(screen);
		tigrPrint(screen, tfont, 10, 10, tigrRGB(0, 0, 0), blf.str().c_str());
		tigrUpdate(screen);
	}
	//if somebody won
	if (win == 1 || win == 2)
	{
		while (!tigrClosed(screen) && !tigrKeyDown(screen, TK_ESCAPE))
		{
			board.draw(screen);
			tigrPrint(screen, tfont, 10, 10, tigrRGB(0, 0, 0), blf.str().c_str());
			tigrPrint(screen, tfont, width / 2-10, height / 2-5, tigrRGB(255*(2-win), 255*(win-1), 0), out.str().c_str());
			tigrUpdate(screen);
		}
	}
	else if (win == -1)
	{
		while (!tigrClosed(screen) && !tigrKeyDown(screen, TK_ESCAPE))
		{
			board.draw(screen);
			tigrPrint(screen, tfont, width / 2 - 10, height / 2 - 5, tigrRGB(100,100,100), out.str().c_str());
			tigrUpdate(screen);
		}
	}
	tigrFree(screen);
	return 0;
}