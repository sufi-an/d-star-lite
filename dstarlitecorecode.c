

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>


#define LARGE  1000000         
       
#define WALLSTOREMOVE 4           
                
#define MAZEWIDTH 21             
#define MAZEHEIGHT 21             
#define STARTX 0                  
#define STARTY 0               
#define GOALX 20                 
#define GOALY 20                  
#define RUNS 5                   
#define HEAPSIZE 100000
#define DIRECTIONS 4

static int dx[DIRECTIONS] = {1, 0, -1,  0};
static int dy[DIRECTIONS] = {0, 1,  0, -1};
static int reverse[DIRECTIONS] = {2, 3, 0, 1};
#define H(cell) 0
int dbg=0;
struct cell;
typedef struct cell cell;

struct cell
{
    cell *move[DIRECTIONS];
    cell *succ[DIRECTIONS];
    cell *searchtree;
    cell *trace;
    int dfsx, dfsy; 
    short obstacle;
    int x, y;
    int g;
    int rhs;
    int key[3];
    int generated;
    int heapindex;
};

cell **maze;
cell *mazestart, *mazegoal; 
int mazeiteration;




cell *heap[HEAPSIZE];
int heapsize = 0;
int keylength = 3;

int keyless(cell *cell1, cell* cell2)//c
{
	
    int keyindex;

    for (keyindex = 0; keyindex < keylength; ++keyindex)//
    {
	if (cell1->key[keyindex] < cell2->key[keyindex])
	    return 1;
	else if (cell1->key[keyindex] > cell2->key[keyindex])
	    return 0;
    }
    return 0;
}



void percolatedown(int hole, cell *tmp)
{
	
    int child;

    if (heapsize != 0)
    {
	for (; 2*hole <= heapsize; hole = child)
        {
	    child = 2*hole;
	    if (child != heapsize && keyless(heap[child+1], heap[child]))
		++child;
	    if (keyless(heap[child], tmp))
            {
		heap[hole] = heap[child];
		heap[hole]->heapindex = hole;
            }
	    else
		break;
        }
	heap[hole] = tmp;
	heap[hole]->heapindex = hole;
    }
}

void percolateup(int hole, cell *tmp)
{

    if (heapsize != 0)
    {
	for (; hole > 1 && keyless(tmp, heap[hole/2]); hole /= 2)//o(logheapsize)
        {
	    heap[hole] = heap[hole/2];
	    heap[hole]->heapindex = hole;
        }
	heap[hole] = tmp;
	heap[hole]->heapindex = hole;
    }
}

void percolateupordown(int hole, cell *tmp)
{
	
	
    if (heapsize != 0)
    {
	if (hole > 1 && keyless(tmp, heap[hole/2]))
	    percolateup(hole, tmp);
	else
	    percolatedown(hole, tmp);
    }
}

void emptyheap(int length)//c
{
	
    int i;

    keylength = length;
    heapsize = 0;
}

cell *topheap()//c
{
	
    if (heapsize == 0)
	return NULL;
    return heap[1];
}

void deleteheap(cell *thiscell)
{
	
    if (thiscell->heapindex != 0 && thiscell->generated == mazeiteration)
    {
	percolateupordown(thiscell->heapindex, heap[heapsize--]);
	thiscell->heapindex = 0;
    }
}



void insertheap(cell *thiscell)
{

    int hole;

    if (thiscell->heapindex == 0 || thiscell->generated != mazeiteration)
    {
	thiscell->heapindex = 0;
	percolateup(++heapsize, thiscell);
    }
    else
	percolateupordown(thiscell->heapindex, heap[thiscell->heapindex]);
}





cell **maze = NULL;
cell *mazestart, *mazegoal;
int mazeiteration = 0;

int goaly = GOALY;
int goalx = GOALX;
int starty = STARTY;
int startx = STARTX;

void preprocessmaze()//o(n^2)
{

    int x, y, d;
    int newx, newy;

    if (maze == NULL)
    {
	maze = (cell **)calloc(MAZEHEIGHT, sizeof(cell *));
	for (y = 0; y < MAZEHEIGHT; ++y)//n=mazeheight
	    maze[y] = (cell *)calloc(MAZEWIDTH, sizeof(cell));
	for (y = 0; y < MAZEHEIGHT; ++y)//n
	    for (x = 0; x < MAZEWIDTH; ++x)//n*n
	    {
		maze[y][x].x = x;
		maze[y][x].y = y;
		for (d = 0; d < DIRECTIONS; ++d)
		{
		    newy = y + dy[d];
		    newx = x + dx[d];
		    maze[y][x].succ[d] = (newy >= 0 && newy < MAZEHEIGHT && newx >= 0 && newx < MAZEWIDTH) ? &maze[newy][newx] : NULL;
		}
	    }
    }

    mazestart = &maze[STARTY][STARTX];
    mazegoal = &maze[GOALY][GOALX];

    mazeiteration = 0;
}

void postprocessmaze()//o(n^2)
{
	
    int x, y;
    int d1, d2;
    cell *tmpcell;

    for (y = 0; y < MAZEHEIGHT; ++y)//n
	for (x = 0; x < MAZEWIDTH; ++x)//n*n
	{
	    maze[y][x].generated = 0;
	    maze[y][x].heapindex = 0; 
	    for (d1 = 0; d1 < DIRECTIONS; ++d1)
		maze[y][x].move[d1] = maze[y][x].succ[d1];
	}
    for (d1 = 0; d1 < DIRECTIONS; ++d1)
	if (mazegoal->move[d1] && mazegoal->move[d1]->obstacle)
	{
	    tmpcell = mazegoal->move[d1];
	    for (d2 = 0; d2 < DIRECTIONS; ++d2)
		if (tmpcell->move[d2])
		{
		    tmpcell->move[d2] = NULL;
		    tmpcell->succ[d2]->move[reverse[d2]] = NULL;
		}
	}
}


void newdfsmaze(int wallstoremove)
{
    int d, dtmp;
    int x, y;
    int newx, newy;
    int randomnumber;
    cell *tmpcell;
    int permute[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    int permutetmp;

    preprocessmaze();//n2
 
    for (y = 0; y < MAZEHEIGHT; ++y)//n2
	for (x = 0; x < MAZEWIDTH; ++x)
	{
	    maze[y][x].obstacle = 1;
	    maze[y][x].dfsx = 0;
	    maze[y][x].dfsy = 0;
	}
    x = 0;
    y = 0;
    maze[y][x].dfsx = -1;
    maze[y][x].dfsy = -1;
	int c=0;
    while (1)
    {
		c++;
	if (maze[y][x].obstacle)
	    maze[y][x].obstacle = 0;
	for (d = 0; d < DIRECTIONS-1; ++d)
	{
	    randomnumber = rand() % (DIRECTIONS-d);
	    permutetmp = permute[randomnumber];
	    permute[randomnumber] = permute[DIRECTIONS-1-d];
	    permute[DIRECTIONS-1-d] = permutetmp;
	}
	for (dtmp = 0; dtmp < DIRECTIONS; ++dtmp)
	{
	    d = permute[dtmp];
	    newx = x + 2*dx[d];
	    newy = y + 2*dy[d];
	    if (maze[y][x].succ[d] != NULL && maze[newy][newx].obstacle)
	    {
		if (maze[y + dy[d]][x + dx[d]].obstacle)
		    maze[y + dy[d]][x + dx[d]].obstacle = 0;
		maze[newy][newx].dfsx = x;
		maze[newy][newx].dfsy = y;
		x = newx;
		y = newy;
		break;
	    }
	}
	if (dtmp == DIRECTIONS)
	{
	    if (maze[y][x].dfsx == -1)
		break;
	    newx = maze[y][x].dfsx;
	    newy = maze[y][x].dfsy;
	    x = newx;
	    y = newy;
	}
    }

    while (wallstoremove)
    {
	newx = rand() % MAZEWIDTH;
	newy = rand() % MAZEHEIGHT;
	if (maze[newy][newx].obstacle)
	{
	    maze[newy][newx].obstacle = 0;
	    --wallstoremove;
	}
    }
    mazegoal->obstacle = 0;

    postprocessmaze();//n2
}

//
int keymodifier;
cell goaltmpcell, oldtmpcell;


void initialize()
{
	
    ++mazeiteration;
    keymodifier = 0;
    mazestart->g = LARGE;
    mazestart->rhs = 0;

    emptyheap(3);//c
    mazestart->key[0] = H(mazestart);
    mazestart->key[1] = H(mazestart) + 1;
    mazestart->key[2] = H(mazestart);



    mazestart->searchtree = NULL;
    mazestart->generated = mazeiteration;
	
    insertheap(mazestart);//0(logheapsize)
    mazegoal->g = LARGE;
    mazegoal->rhs = LARGE;
    mazegoal->searchtree = NULL;
    mazegoal->generated = mazeiteration;
}


void initializecell(cell *thiscell)//c
{
	
    if (thiscell->generated != mazeiteration)
    {
	thiscell->g = LARGE;
	thiscell->rhs = LARGE;
	thiscell->searchtree = NULL;
	thiscell->generated = mazeiteration;
    }
}

void updatecell(cell *thiscell)//logheap
{
	
    if (thiscell->g < thiscell->rhs)
    {

	thiscell->key[0] = thiscell->g + H(thiscell) + keymodifier;
	thiscell->key[1] = thiscell->g + H(thiscell) + keymodifier;
	thiscell->key[2] = thiscell->g;

	insertheap(thiscell);
    }
    else if (thiscell->g > thiscell->rhs)
    {

	thiscell->key[0] = thiscell->rhs + H(thiscell) + keymodifier;
	thiscell->key[1] = thiscell->rhs + H(thiscell) + keymodifier + 1;
	thiscell->key[2] = H(thiscell) + keymodifier;

	insertheap(thiscell);
    }
    else 
	deleteheap(thiscell);
}

void updatekey(cell *thiscell)
{
	
    if (thiscell->g < thiscell->rhs)
    {

	thiscell->key[0] = thiscell->g + H(thiscell) + keymodifier;
	thiscell->key[1] = thiscell->g + H(thiscell) + keymodifier;
	thiscell->key[2] = thiscell->g;

    }
    else 
    {

	thiscell->key[0] = thiscell->rhs + H(thiscell) + keymodifier;
	thiscell->key[1] = thiscell->rhs + H(thiscell) + keymodifier + 1;
	thiscell->key[2] = H(thiscell) + keymodifier;

    }
}

void updaterhs(cell *thiscell)
{
	
    int d;


    thiscell->rhs = LARGE;
    thiscell->searchtree = NULL;

    for (d = 0; d < DIRECTIONS; ++d)
    {

	if (thiscell->move[d] && thiscell->move[d]->generated == mazeiteration && thiscell->rhs > thiscell->move[d]->g + 1)
	{
	    thiscell->rhs = thiscell->move[d]->g + 1;
	    thiscell->searchtree = thiscell->move[d];
	}
    }
    updatecell(thiscell);
}

int computeshortestpath()
{

    cell *tmpcell1, *tmpcell2;
    int x, d;
	
    if (mazegoal->g < mazegoal->rhs)
    {
	goaltmpcell.key[0] = mazegoal->g + keymodifier;
	goaltmpcell.key[1] = mazegoal->g + keymodifier;
	goaltmpcell.key[2] = mazegoal->g;
    }
    else
    {
	goaltmpcell.key[0] = mazegoal->rhs + keymodifier;
	goaltmpcell.key[1] = mazegoal->rhs + keymodifier + 1;
	goaltmpcell.key[2] = keymodifier;
    }

    while (topheap() && (mazegoal->rhs > mazegoal->g || keyless(topheap(), &goaltmpcell)))//m*logheap*logheap
    {
	tmpcell1 = topheap();//c
	oldtmpcell.key[0] = tmpcell1->key[0];
	oldtmpcell.key[1] = tmpcell1->key[1];

	oldtmpcell.key[2] = tmpcell1->key[2];

	updatekey(tmpcell1);//c 
	if (keyless(&oldtmpcell, tmpcell1))
	    updatecell(tmpcell1);//logheapsize
	else if (tmpcell1->g > tmpcell1->rhs)
	{
	    tmpcell1->g = tmpcell1->rhs;
	    deleteheap(tmpcell1);//logheapsize

	    for (d = 0; d < DIRECTIONS; ++d)//logheapsize
	    {

		if (tmpcell1->move[d])
		{
		    tmpcell2 = tmpcell1->move[d];
		    initializecell(tmpcell2);//c
		    if (tmpcell2 != mazestart && tmpcell2->rhs > tmpcell1->g + 1)
		    {
			tmpcell2->rhs = tmpcell1->g + 1;
			tmpcell2->searchtree = tmpcell1;
			updatecell(tmpcell2);//log heap*log heap
		    }
		}
	    }
	}
      else//logheap
      {
	  tmpcell1->g = LARGE;
	  updatecell(tmpcell1);//log heap

	  for (d = 0; d < DIRECTIONS; ++d) 
	  {

	      if (tmpcell1->move[d])
	      {
		  tmpcell2 = tmpcell1->move[d];
		  initializecell(tmpcell2);//c
		  if (tmpcell2 != mazestart && tmpcell2->searchtree == tmpcell1)
		      updaterhs(tmpcell2);//logheap
	      }
	  }
      }

	if (mazegoal->g < mazegoal->rhs)
	{
	    goaltmpcell.key[0] = mazegoal->g + keymodifier;
	    goaltmpcell.key[1] = mazegoal->g + keymodifier;
	    goaltmpcell.key[2] = mazegoal->g;
	}
	else
	{
	    goaltmpcell.key[0] = mazegoal->rhs + keymodifier;
	    goaltmpcell.key[1] = mazegoal->rhs + keymodifier + 1;
	    goaltmpcell.key[2] = keymodifier;
	}    

    }

  return (mazegoal->rhs == LARGE);
}

void updatemaze(cell *robot)
{

	
    int d1, d2;
    cell *tmpcell;


    for (d1 = 0; d1 < DIRECTIONS; ++d1)
    {

	if (robot->move[d1] && robot->move[d1]->obstacle)
	{
	    tmpcell = robot->move[d1];
	    initializecell(tmpcell);
	    for (d2 = 0; d2 < DIRECTIONS; ++d2)
		if (tmpcell->move[d2])
		{
		    tmpcell->move[d2] = NULL;
		    tmpcell->succ[d2]->move[reverse[d2]] = NULL;
		    initializecell(tmpcell->succ[d2]);
		    if (tmpcell->succ[d2] != mazestart && tmpcell->succ[d2]->searchtree == tmpcell)
			updaterhs(tmpcell->succ[d2]);
		}
	    if (tmpcell != mazestart)
	    {
		tmpcell->rhs = LARGE;
		updatecell(tmpcell);
	    }
	}
    }
}

void printknownmaze()
{
    int x, y, d;
    static char **display = NULL;
    cell *tmpcell;

    if (display == NULL)
    {
	display = (char **)calloc(MAZEHEIGHT, sizeof(char *));
	for (y = 0; y < MAZEHEIGHT; ++y)
	    display[y] = (char *)calloc(MAZEWIDTH, sizeof(char));
    }
    for (y = 0; y < MAZEHEIGHT; ++y)
	for (x = 0; x < MAZEWIDTH; ++x)
	    {
		display[y][x] = 'X';
		for (d = 0; d < DIRECTIONS; ++d)
		    if (maze[y][x].move[d])
			display[y][x] = ' ';
	    }
    for (tmpcell = mazegoal; tmpcell != mazestart; tmpcell = tmpcell->searchtree)
	display[tmpcell->y][tmpcell->x] = '.';
    display[mazestart->y][mazestart->x] = 'G';
    display[mazegoal->y][mazegoal->x] = 'R';
    for (x = 0; x < MAZEWIDTH+2; ++x)
	printf( "X");
    printf( "\n");
    for (y = 0; y < MAZEHEIGHT; ++y)
    {
	printf( "X");
	for (x = 0; x < MAZEWIDTH; ++x)
	    printf( "%c", display[y][x]);
	printf( "X\n");
    }
    for (x = 0; x < MAZEWIDTH+2; ++x)
	printf( "X");
    printf( "\n\n\n");
}
int main()
{

    int k, l;
    cell *tmpcell;
    cell *lastcell;

	int flag=1;
	int count=0;
		int validmazecount=0;
    for (k = 0; k < RUNS; ++k)
    {
	printf("maze %d\n", k);

	newdfsmaze(WALLSTOREMOVE);//
	
	initialize();//0(logheapsize)

	lastcell = mazegoal;
	while (mazestart != mazegoal)
	{

	    if (computeshortestpath())//number of v * logheap*logheap ;as heap stores connectable v ;so it is v*logv*logv=v*logv 
		break;
		
		printknownmaze();
		
		//this part updates the maze in runtime
	    mazegoal->trace = NULL;
  		do
	    {
		mazegoal->searchtree->trace = mazegoal;
		mazegoal = mazegoal->searchtree;
	    } while (mazestart != mazegoal && !mazegoal->searchtree->obstacle);
	    if (mazestart != mazegoal)
	    {
		keymodifier += H(lastcell);
		lastcell = mazegoal;
		for (tmpcell=mazegoal; tmpcell; tmpcell=tmpcell->trace)
		    updatemaze(tmpcell);
	    }
	
	}
    }
	
 }
