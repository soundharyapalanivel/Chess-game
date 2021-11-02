# This program is a chess game. The user may play against a friend or the
# computer.
#
# The game state is mainly stored as a 2D list of strings, and most of the
# processing is thus done on a list of strings.
#
# The GUI takes the current state and displays it on the screen. The GUI allows
# drag and drop movement of pieces,click-click movement and voice movement.
#
# The AI that plays against the human evaluates all possible moves made by either
# player up to a certain level of depth. The AI evaluates each position by giving
# it a score. The higher the value of the score, the more favourable a position
# is for white and the lower the value of the score, the more favourable the
# position is for black. Knowing that white will try to get the score to be higher
# and black will try and get the score to be lower, the AI assumes best play from
# either side as it traverses up the search tree and chooses the best move to be
# played. A problem that may arise is the number of postions that need to be
# evaulated. Even at 3 levels of depth, thousands of positions have to be
# evaluatd.
# Several methods are used in this program to reduce positions that are searched:
# 1. Alpha-beta pruning: As a result of  evaluating a position it can be found
# that a portion of the search tree can be ignored as no further evaluations can
# guarantee better results. This can happen because white and black area against
# one another. White plays what is best for it and black plays what is best for it,
# so it would make sense for white to ignore any portion of the tree where black
# has a clear upperhand that it can choose to play.
# 2. Transposition table: Often, two different pathways in a search tree can result
# in the same board being evaluated. Instead of evaluating the same board several
# times, the program stores a table of values in a dictionary where the keys are
# the positions. This way, repeated positions can have their evaluations looked up
# fairly quickly, as the board state is hashed.
# 3. Opening Book - The opening book is again a dictionary that stores board
# positions often seen in the beginning few moves in chess. Appropraite moves that
# can be played at such positions is stored in the dictionary. A random move is
# selected and played from the list of suggested moves wihtout searching if the AI
# finds itself confronting a such a board postion. Note that this opening book was
# recorded by myself and so it does not have many positions stored in it.
#
# In order to traverse the search tree as above, the AI needs to know how to evaluate the
# board at any position to decide if white or black has the advantage. My evaluation
# function currently looks at three main things when evaluating the board:
#    a) Material for white and black. Each piece has a value and the more pieces you have,
#        the better off your position is likely to be. For example, if white has an extra
#        queen, it has an advantage over black.
#    b) Piece-square table values - for each piece, there is a table that stores the best
#        squares that the particular piece should occupy. So if white has a knight at a
#        good square that controls the centre of the board, whereas black has a knight
#        at the corner of the board, the situation is evaluated as being more favourable
#        for white.
#    c) Reduction in points for doubled pawns, isolated pawns, and blocked pawns. If any
#        side has a set of pawns with the above features their points are slightly lower
#        to indicate a slight disadvantage in such a position.
#    d) A checkmate: a position where this has occured gets a very high point, so that the
#        AI moves towards this if it can. (or avoids it).

#Import dependencies:
import pygame #Game library
from pygame.locals import * #For useful variables..for eg QUIT
import copy #Library used to make exact copies of lists.
import pickle #Library used to store dictionaries in a text file and read them from text files.
import random #Used for making random selections
from collections import defaultdict #Used for giving dictionary values default data types.
from collections import Counter #For counting elements in a list effieciently.
import threading #To allow for AI to think simultaneously while the GUI is coloring the board.
import time
import speech_recognition as sr
from tkinter import*
import tkinter.messagebox

play_sound=True


class GamePosition:
    
    def __init__(self,board,player,castling_rights,EnP_Target,HMC,history = {}):
        # Making an object of Commands Class
        self.c=Commands()
        # A 2D array containing information about piece postitions. Check main function to see an example of such
        # a representation.
        self.board = board
        # Stores 0 or 1. If white to play, equals 0. If black to play, stores 1.
        self.player = player
        # A list that contains castling rights for white and black. Each castling right is a list that contains right
        # to castle kingside and queenside.
        # Stores the coordinates of a square that can be targeted by en passant capture.
        self.EnP = EnP_Target
        self.castling = castling_rights
        # Half move clock. Stores the number of irreversible moves made so far, in order to help
        # detect draw by 50 moves without any capture or pawn movement.
        self.HMC = HMC
        # A dictionary that stores as key a position (hashed) and the value of each of
        # these keys represents the number of times each of these positions was repeated in order for this
        # position to be reached.
        self.history = history

    def getboard(self):
        return self.board
    def setboard(self,board):
        self.board = board
    def getplayer(self):
        return self.player
    def setplayer(self,player):
        self.player = player
    def getCastleRights(self):
        return self.castling
    def setCastleRights(self,castling_rights):
        self.castling = castling_rights
    def getEnP(self):
        return self.EnP
    def setEnP(self, EnP_Target):
        self.EnP = EnP_Target
    def getHMC(self):
        return self.HMC
    def setHMC(self,HMC):
        self.HMC = HMC
    def checkRepition(self):
        # Returns True if any of of the values in the history dictionary is greater than 3.
        # This would mean a position had been repeated at least thrice in order to reach the
        # current position in this game.
        return any(value>=3 for value in self.history.values())
    def addtoHistory(self,position):
        # Generate a unique key out of the current position:
        key = self.c.pos2key(position)
        #Add it to the history dictionary.
        self.history[key] = self.history.get(key,0) + 1
    def gethistory(self):
        return self.history
    def clone(self):
        # This method returns another instance of the current object with exactly the same
        # parameters but independent of the current object.
        clone = GamePosition(copy.deepcopy(self.board),    #  Independent copy
                             self.player,
                             copy.deepcopy(self.castling), #  Independent copy
                             self.EnP,
                             self.HMC)
        return clone


class Shades:
    """
    It is used to shade the board
    """
    def __init__(self,image,coord):
        self.image = image
        self.pos = coord
    def getInfo(self):
        return [self.image,self.pos]


class Piece:
    """
    Piece clips the sprite into pieces to display on the board
    """
    def __init__(self,pieceinfo,chess_coord,square_width, square_height):
        # pieceinfo is a string such as 'Qb'. The Q represents Queen and b
        # shows the fact that it is black:
        piece = pieceinfo[0]
        color = pieceinfo[1]
        # Get the information about where the image for this piece is stored
        # on the overall sprite image with all the pieces. Note that
        # square_width and square_height represent the size of a square on the
        # chess board.
        if piece=='K':
            index = 0
        elif piece=='Q':
            index = 1
        elif piece=='B':
            index = 2
        elif piece == 'N':
            index = 3
        elif piece == 'R':
            index = 4
        elif piece == 'P':
            index = 5
        left_x =square_width*index
        if color == 'w':
            left_y = 0
        else:
            left_y = square_height

        self.pieceinfo = pieceinfo
        # subsection defines the part of the sprite image that represents our
        # piece
        self.subsection = (left_x,left_y,square_width,square_height)
        # There are two ways that the position of a piece is defined on the
        # board.
        # The default one used is the chess_coord, which stores something
        # like (3,2). It represents the chess coordinate where our piece image should
        # be blitted. On the other hand, is pos does not hold the default value
        # of (-1,-1), it will hold pixel coordinates such as (420,360) that represents
        # the location in the window that the piece should be blitted on. This is
        # useful for example if our piece is transitioning from a square to another:
        self.chess_coord = chess_coord
        self.pos = (-1,-1)

    def getInfo(self):
        return [self.chess_coord, self.subsection,self.pos]
    def setpos(self,pos):
        self.pos = pos
    def getpos(self):
        return self.pos
    def setcoord(self,coord):
        self.chess_coord = coord


class Commands:
    """
    this class works with variables that hold the information about game state.
    it contains chess processing functions
    """

    def isOccupied(self,board,x,y):
        # isOccupied(board,x,y) - Returns true if a given coordinate on the board is not empty, and
        # false otherwise.
        if board[int(y)][int(x)] == 0:
        # The square has nothing on it.
            return False
        return True

    def isOccupiedby(self,board,x,y,color):
        # isOccupiedby(board,x,y,color) - Same as above, but only returns true if the square
        # specified by the coordinates is of the specific color inputted.
        if board[y][x] == 0:
            # the square has nothing on it.
            return False
        if board[y][x][1] == color[0]:
            # The square has a piece of the color inputted.
            return True
        # The square has a piece of the opposite color.
        return False

    def filterbyColor(self,board,listofTuples,color):
        # filterbyColor(board,listofTuples,color) - This function takes the board state, a list
        # of coordinates, and a color as input. It will return the same list, but without
        # coordinates that are out of bounds of the board and also without those occupied by the
        # pieces of the particular color passed to this function as an argument. In other words,
        # if 'white' is passed in, it will not return any white occupied square.
        filtered_list = []
        # Go through each coordinate:
        for pos in listofTuples:
            x = pos[0]
            y = pos[1]
            if x>=0 and x<=7 and y>=0 and y<=7 and not self.isOccupiedby(board,x,y,color):
                # coordinates are on-board and no same-color piece is on the square.
                filtered_list.append(pos)
        return filtered_list

    def lookfor(self,board,piece):
        # lookfor(board,piece) - This functions takes the 2D array that represents a board and finds
        # the indices of all the locations that is occupied by the specified piece. The list of
        # indices is returned.
        listofLocations = []
        for row in range(8):
            for col in range(8):
                if board[row][col] == piece:
                    x = col
                    y = row
                    listofLocations.append((x,y))
        return listofLocations


    def isAttackedby(self,position,target_x,target_y,color):
        # isAttackedby(position,target_x,target_y,color) - This function checks if the square specified
        # by (target_x,target_y) coordinates is being attacked by any of a specific colored set of pieces.

        # Get board
        board = position.getboard()
        # Get b from black or w from white
        color = color[0]
        # Get all the squares that are attacked by the particular side:
        listofAttackedSquares = []
        for x in range(8):
            for y in range(8):
                if board[y][x]!=0 and board[y][x][1]==color:
                    listofAttackedSquares.extend(
                        self.findPossibleSquares(position,x,y,True)) #The true argument
                    # prevents infinite recursion.
        # Check if the target square falls under the range of attack by the specified
        # side, and return it:
        return (target_x,target_y) in listofAttackedSquares

    def findPossibleSquares(self,position,x,y,AttackSearch=False):
        # findPossibleSquares(position,x,y,AttackSearch=False) - This function takes as its input the
        # current state of the chessboard, and a particular x and y coordinate. It will return for the
        # piece on that board a list of possible coordinates it could move to, including captures and
        # excluding illegal moves (eg moves that leave a king under check). AtttackSearch is an
        # argument used to ensure infinite recursions do not occur.

        # Get individual component data from the position object:
        board = position.getboard()
        player = position.getplayer()
        castling_rights = position.getCastleRights()
        EnP_Target = position.getEnP()

        # In case something goes wrong:
        piece = board[y][x][0] #Pawn, rook, etc.
        color = board[y][x][1] #w or b.

        # Have the complimentary color stored for convenience:
        enemy_color = self.opp(color)
        listofTuples = [] #Holds list of attacked squares.

        if piece == 'P': #The piece is a pawn.
            if color=='w': #The piece is white
                if not self.isOccupied(board,x,y-1) and not AttackSearch:
                    #The piece immediately above is not occupied, append it.
                    listofTuples.append((x,y-1))

                    if y == 6 and not self.isOccupied(board,x,y-2):
                        #If pawn is at its initial position, it can move two squares.
                        listofTuples.append((x,y-2))

                if x!=0 and self.isOccupiedby(board,x-1,y-1,'black'):
                    #The piece diagonally up and left of this pawn is a black piece.
                    #Also, this is not an 'a' file pawn (left edge pawn)
                    listofTuples.append((x-1,y-1))
                if x!=7 and self.isOccupiedby(board,x+1,y-1,'black'):
                    #The piece diagonally up and right of this pawn is a black one.
                    #Also, this is not an 'h' file pawn.
                    listofTuples.append((x+1,y-1))
                if EnP_Target!=-1: #There is a possible en pasant target:
                    if EnP_Target == (x-1,y-1) or EnP_Target == (x+1,y-1):
                        #We're at the correct location to potentially perform en
                        #passant:
                        listofTuples.append(EnP_Target)

            elif color=='b': #The piece is black, same as above but opposite side.
                if not self.isOccupied(board,x,y+1) and not AttackSearch:
                    listofTuples.append((x,y+1))
                    if y == 1 and not self.isOccupied(board,x,y+2):
                        listofTuples.append((x,y+2))
                if x!=0 and self.isOccupiedby(board,x-1,y+1,'white'):
                    listofTuples.append((x-1,y+1))
                if x!=7 and self.isOccupiedby(board,x+1,y+1,'white'):
                    listofTuples.append((x+1,y+1))
                if EnP_Target == (x-1,y+1) or EnP_Target == (x+1,y+1):
                    listofTuples.append(EnP_Target)

        elif piece == 'R': #The piece is a rook.
            #Get all the horizontal squares:
            for i in [-1,1]:
                #i is -1 then +1. This allows for searching right and left.
                kx = x #This variable stores the x coordinate being looked at.
                while True: #loop till break.
                    kx = kx + i #Searching left or right
                    if kx<=7 and kx>=0: #Making sure we're still in board.

                        if not self.isOccupied(board,kx,y):
                            #The square being looked at it empty. Our rook can move
                            #here.
                            listofTuples.append((kx,y))
                        else:
                            #The sqaure being looked at is occupied. If an enemy
                            #piece is occupying it, it can be captured so its a valid
                            #move.
                            if self.isOccupiedby(board,kx,y,enemy_color):
                                listofTuples.append((kx,y))
                            #Regardless of the occupying piece color, the rook cannot
                            #jump over. No point continuing search beyond in this
                            #direction:
                            break

                    else: #We have exceeded the limits of the board
                        break
            #Now using the same method, get the vertical squares:
            for i in [-1,1]:
                ky = y
                while True:
                    ky = ky + i
                    if ky<=7 and ky>=0:
                        if not self.isOccupied(board,x,ky):
                            listofTuples.append((x,ky))
                        else:
                            if self.isOccupiedby(board,x,ky,enemy_color):
                                listofTuples.append((x,ky))
                            break
                    else:
                        break

        elif piece == 'N': #The piece is a knight.
            #The knight can jump across a board. It can jump either two or one
            #squares in the x or y direction, but must jump the complimentary amount
            #in the other. In other words, if it jumps 2 sqaures in the x direction,
            #it must jump one square in the y direction and vice versa.
            for dx in [-2,-1,1,2]:
                if abs(dx)==1:
                    sy = 2
                else:
                    sy = 1
                for dy in [-sy,+sy]:
                    listofTuples.append((x+dx,y+dy))
            #Filter the list of tuples so that only valid squares exist.
            listofTuples = self.filterbyColor(board,listofTuples,color)
        elif piece == 'B': # A bishop.
            #A bishop moves diagonally. This means a change in x is accompanied by a
            #change in y-coordiante when the piece moves. The changes are exactly the
            #same in magnitude and direction.
            for dx in [-1,1]: #Allow two directions in x.
                for dy in [-1,1]: #Similarly, up and down for y.
                    kx = x #These varibales store the coordinates of the square being
                           #observed.
                    ky = y
                    while True: #loop till broken.
                        kx = kx + dx #change x
                        ky = ky + dy #change y
                        if kx<=7 and kx>=0 and ky<=7 and ky>=0:
                            #square is on the board
                            if not self.isOccupied(board,kx,ky):
                                #The square is empty, so our bishop can go there.
                                listofTuples.append((kx,ky))
                            else:
                                #The square is not empty. If it has a piece of the
                                #enemy,our bishop can capture it:
                                if self.isOccupiedby(board,kx,ky,enemy_color):
                                    listofTuples.append((kx,ky))
                                #Bishops cannot jump over other pieces so terminate
                                #the search here:
                                break
                        else:
                            #Square is not on board. Stop looking for more in this
                            #direction:
                            break

        elif piece == 'Q': #A queen
            #A queen's possible targets are the union of all targets that a rook and
            #a bishop could have made from the same location
            #Temporarily pretend there is a rook on the spot:
            board[y][x] = 'R' + color
            list_rook = self.findPossibleSquares(position,x,y,True)
            #Temporarily pretend there is a bishop:
            board[y][x] = 'B' + color
            list_bishop = self.findPossibleSquares(position,x,y,True)
            #Merge the lists:
            listofTuples = list_rook + list_bishop
            #Change the piece back to a queen:
            board[y][x] = 'Q' + color
        elif piece == 'K': # A king!
            #A king can make one step in any direction:
            for dx in [-1,0,1]:
                for dy in [-1,0,1]:
                    listofTuples.append((x+dx,y+dy))
            #Make sure the targets aren't our own piece or off-board:
            listofTuples = self.filterbyColor(board,listofTuples,color)
            if not AttackSearch:
                #Kings can potentially castle:
                right = castling_rights[player]
                #Kingside
                if (right[0] and #has right to castle
                board[y][7]!=0 and #The rook square is not empty
                board[y][7][0]=='R' and #There is a rook at the appropriate place
                not self.isOccupied(board,x+1,y) and #The square on its right is empty
                not self.isOccupied(board,x+2,y) and #The second square beyond is also empty
                not self.isAttackedby(position,x,y,enemy_color) and #The king isn't under atack
                not self.isAttackedby(position,x+1,y,enemy_color) and #Or the path through which
                not self.isAttackedby(position,x+2,y,enemy_color)):#it will move
                    listofTuples.append((x+2,y))
                #Queenside
                if (right[1] and #has right to castle
                board[y][0]!=0 and #The rook square is not empty
                board[y][0][0]=='R' and #The rook square is not empty
                not self.isOccupied(board,x-1,y)and #The square on its left is empty
                not self.isOccupied(board,x-2,y)and #The second square beyond is also empty
                not self.isOccupied(board,x-3,y) and #And the one beyond.
                not self.isAttackedby(position,x,y,enemy_color) and #The king isn't under atack
                not self.isAttackedby(position,x-1,y,enemy_color) and #Or the path through which
                not self.isAttackedby(position,x-2,y,enemy_color)):#it will move
                    listofTuples.append((x-2,y)) #Let castling be an option.

        # Make sure the king is not under attack as a result of this move:
        if not AttackSearch:
            new_list = []
            for tupleq in listofTuples:
                x2 = int(tupleq[0])
                y2 = int(tupleq[1])
                temp_pos = position.clone()
                self.makemove(temp_pos,x,y,x2,y2)
                if not self.isCheck(temp_pos,color):
                    new_list.append(tupleq)
            listofTuples = new_list
        return listofTuples

    def makemove(self,position,x,y,x2,y2):
        # makemove(position,x,y,x2,y2) - This function makes a move on the board. The position object
        # gets updated here with new information. (x,y) are coordinates of the piece to be moved, and
        # (x2,y2) are coordinates of the destination. (x2,y2) being correct destination (ie the move
        # a valid one) is not checked for and is assumed to be the case.

        # Get data from the position:
        x = int(x)
        y = int(y)
        x2 = int(x2)
        y2 = int(y2)
        board = position.getboard()
        piece = board[y][x]
        if piece==0:
            return
        piece=piece[0]
        color = board[y][x][1]
        #Get the individual game components:
        player = position.getplayer()
        castling_rights = position.getCastleRights()
        EnP_Target = position.getEnP()
        half_move_clock = position.getHMC()
        #Update the half move clock:
        if self.isOccupied(board,x2,y2) or piece=='P':
            #Either a capture was made or a pawn has moved:
            half_move_clock = 0
        else:
            #An irreversible move was played:
            half_move_clock += 1

        #Make the move:
        board[y2][x2] = board[y][x]
        board[y][x] = 0

        #Special piece requirements:
        #King:
        if piece == 'K':
            #Ensure that since a King is moved, the castling
            #rights are lost:
            castling_rights[player] = [False,False]
            #If castling occured, place the rook at the appropriate location:
            if abs(x2-x) == 2:
                if color=='w':
                    l = 7
                else:
                    l = 0

                if x2>x:
                        board[l][5] = 'R'+color
                        board[l][7] = 0
                else:
                        board[l][3] = 'R'+color
                        board[l][0] = 0
        #Rook:
        if piece=='R':
            #The rook moved. Castling right for this rook must be removed.
            if x==0 and y==0:
                #Black queenside
                castling_rights[1][1] = False
            elif x==7 and y==0:
                #Black kingside
                castling_rights[1][0] = False
            elif x==0 and y==7:
                #White queenside
                castling_rights[0][1] = False
            elif x==7 and y==7:
                #White kingside
                castling_rights[0][0] = False
        #Pawn:
        if piece == 'P':
            #If an en passant kill was made, the target enemy must die:
            if EnP_Target == (x2,y2):
                if color=='w':
                    board[y2+1][x2] = 0
                else:
                    board[y2-1][x2] = 0
            #If a pawn moved two steps, there is a potential en passant
            #target. Otherise, there isn't. Update the variable:
            if abs(y2-y)==2:
                EnP_Target = (x,(y+y2)/2)
            else:
                EnP_Target = -1
            #If a pawn moves towards the end of the board, it needs to
            #be promoted. Note that in this game a pawn is being promoted
            #to a queen regardless of user choice.
            if y2==0:
                board[y2][x2] = 'Qw'
            elif y2 == 7:
                board[y2][x2] = 'Qb'
        else:
            #If a pawn did not move, the en passsant target is gone as well,
            #since a turn has passed:
            EnP_Target = -1

        #Since a move has been made, the other player
        #should be the 'side to move'
        player = 1 - player
        #Update the position data:
        position.setplayer(player)
        position.setCastleRights(castling_rights)
        position.setEnP(EnP_Target)
        position.setHMC(half_move_clock)
    def opp(self,color):
        # opp(color) - Returns the complimentary color to the one passed. So inputting 'black' returns
        # 'w', for example.
        color = color[0]
        if color == 'w':
            oppcolor = 'b'
        else:
            oppcolor = 'w'
        return oppcolor
    def isCheck(self,position,color):
        # isCheck(position,color) - This function takes a position as its input and checks if the
        # King of the specified color is under attack by the enemy. Returns true if that is the case,
        # and false otherwise.
        #Get data:
        board = position.getboard()
        color = color[0]
        enemy = self.opp(color)
        piece = 'K' + color
        #Get the coordinates of the king:
        x,y = self.lookfor(board,piece)[0]
        #Check if the position of the king is attacked by
        #the enemy and return the result:
        return self.isAttackedby(position,x,y,enemy)
    def isCheckmate(self,position,color=-1):
        # isCheckmate(position,color=-1) - This function tells you if a position is a checkmate.
        # Color is an optional argument that may be passed to specifically check for mate against a
        # specific color.
        if color==-1:
            return self.isCheckmate(position,'white') or self.isCheckmate(position,'b')
        color = color[0]
        if self.isCheck(position,color) and self.allMoves(position,color)==[]:
            #The king casis under attack, and there are no possible moves for this side to make:
                return True
        #Either the king is not under attack or there are possible moves to be played:
        return False
    def isStalemate(self,position):
        # isStalemate(position) - This function checks if a particular position is a stalemate.
        # If it is, it returns true, otherwise it returns false.
        #Get player to move:
        player = position.getplayer()
        #Get color:
        if player==0:
            color = 'w'
        else:
            color = 'b'
        if not self.isCheck(position,color) and self.allMoves(position,color)==[]:
            #The player to move is not under check yet cannot make a move.
            #It is a stalemate.
            return True
        return False
    def getallpieces(self,position,color):
        # getallpieces(position,color) - This function returns a list of positions of all the pieces on
        # the board of a particular color.

        #Get the board:
        board = position.getboard()
        listofpos = []
        for j in range(8):
            for i in range(8):
                if self.isOccupiedby(board,i,j,color):
                    listofpos.append((i,j))
        return listofpos
    def allMoves(self,position, color):
        # allMoves(position, color) - This function takes as its argument a position and a color/colorsign
        # that represents a side. It generates a list of all possible moves for that side and returns it.
        #Find if it is white to play or black:
        if color==1:
            color = 'white'
        elif color ==-1:
            color = 'black'
        color = color[0]
        #Get all pieces controlled by this side:
        listofpieces = self.getallpieces(position,color)
        moves = []
        #Loop through each piece:
        for pos in listofpieces:
            #For each piece, find all the targets it can attack:
            targets = self.findPossibleSquares(position,pos[0],pos[1])
            for target in targets:
                #Save them all as possible moves:
                 moves.append([pos,target])
        return moves
    def pos2key(self,position):
        # pos2key(position) - This function takes a position as input argument. For this particular
        # position, it will generate a unique key that can be used in a dictionary by making it hashable.
        #Get board:
        board = position.getboard()
        #Convert the board into a tuple so it is hashable:
        boardTuple = []
        for row in board:
            boardTuple.append(tuple(row))
        boardTuple = tuple(boardTuple)
        #Get castling rights:
        rights = position.getCastleRights()
        #Convert to a tuple:
        tuplerights = (tuple(rights[0]),tuple(rights[1]))
        #Generate the key, which is a tuple that also takes into account the side to play:
        key = (boardTuple,position.getplayer(),
               tuplerights)
        #Return the key:
        return key


###########################////////AI RELATED FUNCTIONS\\\\\\\\\\############################

class AI:

    def __init__(self):
        self.c=Commands()

    def negamax( self,position,depth,alpha,beta,colorsign,bestMoveReturn,openings,searched,root=True):
        #First check if the position is already stored in the opening database dictionary:
        if root:
            #Generate key from current position:
            key = self.c.pos2key(position)
            if key in openings:
                #Return the best move to be played:
                bestMoveReturn[:] = random.choice(openings[key])
                return
        #Access global variable that will store scores of positions already evaluated:

        #If the depth is zero, we are at a leaf node (no more depth to be analysed):
        if depth==0:
            return colorsign*self.evaluate(position)
        #Generate all the moves that can be played:
        moves = self.c.allMoves(position, colorsign)
        #If there are no moves to be played, just evaluate the position and return it:
        if moves==[]:
            return colorsign*self.evaluate(position)
        #Initialize a best move for the root node:
        if root:
            bestMove = moves[0]
        #Initialize the best move's value:
        bestValue = -100000
        #Go through each move:
        for move in moves:
            #Make a clone of the current move and perform the move on it:
            newpos = position.clone()
            self.c.makemove(newpos,move[0][0],move[0][1],move[1][0],move[1][1])
            #Generate the key for the new resulting position:
            key = self.c.pos2key(newpos)
            #If this position was already searched before, retrieve its node value.
            #Otherwise, calculate its node value and store it in the dictionary:
            if key in searched:
                value = searched[key]
            else:
                value = -self.negamax(newpos,depth-1, -beta,-alpha,-colorsign,[],openings,searched,False)
                searched[key] = value
            #If this move is better than the best so far:
            if value>bestValue:
                #Store it
                bestValue = value
                #If we're at root node, store the move as the best move:
                if root:
                    bestMove = move
            #Update the lower bound for this node:
            alpha = max(alpha,value)
            if alpha>=beta:
                #If our lower bound is higher than the upper bound for this node, there
                #is no need to look at further moves:
                break
        #If this is the root node, return the best move:
        if root:
            searched = {}
            bestMoveReturn[:] = bestMove
            return
        #Otherwise, return the bestValue (i.e. value for this node.)
        return bestValue
    def evaluate(self,position):

        if self.c.isCheckmate(position,'white'):
            #Major advantage to black
            return -20000
        if self.c.isCheckmate(position,'black'):
            #Major advantage to white
            return 20000
        #Get the board:
        board = position.getboard()
        #Flatten the board to a 1D array for faster calculations:
        flatboard = [x for row in board for x in row]
        #Create a counter object to count number of each pieces:
        c = Counter(flatboard)
        Qw = c['Qw']
        Qb = c['Qb']
        Rw = c['Rw']
        Rb = c['Rb']
        Bw = c['Bw']
        Bb = c['Bb']
        Nw = c['Nw']
        Nb = c['Nb']
        Pw = c['Pw']
        Pb = c['Pb']
        #Note: The above choices to flatten the board and to use a library
        #to count pieces were attempts at making the AI more efficient.
        #Perhaps using a 1D board throughout the entire program is one way
        #to make the code more efficient.
        #Calculate amount of material on both sides and the number of moves
        #played so far in order to determine game phase:
        whiteMaterial = 9*Qw + 5*Rw + 3*Nw + 3*Bw + 1*Pw
        blackMaterial = 9*Qb + 5*Rb + 3*Nb + 3*Bb + 1*Pb
        numofmoves = len(position.gethistory())
        gamephase = 'opening'
        if numofmoves>40 or (whiteMaterial<14 and blackMaterial<14):
            gamephase = 'ending'
        #A note again: Determining game phase is again one the attempts
        #to make the AI smarter when analysing boards and has not been
        #implemented to its full potential.
        #Calculate number of doubled, blocked, and isolated pawns for
        #both sides:
        Dw = self.doubledPawns(board,'white')
        Db = self.doubledPawns(board,'black')
        Sw = self.blockedPawns(board,'white')
        Sb = self.blockedPawns(board,'black')
        Iw = self.isolatedPawns(board,'white')
        Ib = self.isolatedPawns(board,'black')
        #Evaluate position based on above data:
        evaluation1 = 900*(Qw - Qb) + 500*(Rw - Rb) +330*(Bw-Bb
                    )+320*(Nw - Nb) +100*(Pw - Pb) +-30*(Dw-Db + Sw-Sb + Iw- Ib
                    )
        #Evaluate position based on piece square tables:
        evaluation2 = self.pieceSquareTable(flatboard,gamephase)
        #Sum the evaluations:
        evaluation = evaluation1 + evaluation2
        #Return it:
        return evaluation
    def pieceSquareTable(self,flatboard,gamephase):
        #Initialize score:
        p=PieceTable()
        score = 0
        #Go through each square:
        for i in range(64):
            if flatboard[i]==0:
                #Empty square
                continue
            #Get data:
            piece = flatboard[i][0]
            color = flatboard[i][1]
            sign = +1
            #Adjust index if black piece, since piece sqaure tables
            #were designed for white:
            if color=='b':
                i = ((7-i)//8)*8 + i%8
                sign = -1
            #Adjust score:
            if piece=='P':
                score += sign*p.pawn_table[i]
            elif piece=='N':
                score+= sign*p.knight_table[i]
            elif piece=='B':
                score+=sign*p.bishop_table[i]
            elif piece=='R':
                score+=sign*p.rook_table[i]
            elif piece=='Q':
                score+=sign*p.queen_table[i]
            elif piece=='K':
                #King has different table values based on phase
                #of the game:
                if gamephase=='opening':
                    score+=sign*p.king_table[i]
                else:
                    score+=sign*p.king_endgame_table[i]
        return score
    def doubledPawns(self,board,color):

        color = color[0]
        #Get indices of pawns:
        listofpawns = self.c.lookfor(board,'P'+color)
        #Count the number of doubled pawns by counting occurences of
        #repeats in their x-coordinates:
        repeats = 0
        temp = []
        for pawnpos in listofpawns:
            if pawnpos[0] in temp:
                repeats = repeats + 1
            else:
                temp.append(pawnpos[0])
        return repeats
    def blockedPawns(self,board,color):

        color = color[0]
        listofpawns = self.c.lookfor(board,'P'+color)
        blocked = 0
        #Self explanatory:
        for pawnpos in listofpawns:
            if ((color=='w' and self.c.isOccupiedby(board,pawnpos[0],pawnpos[1]-1,
                                           'black'))
                or (color=='b' and self.c.isOccupiedby(board,pawnpos[0],pawnpos[1]+1,
                                           'white'))):
                blocked = blocked + 1
        return blocked
    def isolatedPawns(self,board,color):

        color = color[0]
        listofpawns = self.c.lookfor(board,'P'+color)
        #Get x coordinates of all the pawns:
        xlist = [x for (x,y) in listofpawns]
        isolated = 0
        for x in xlist:
            if x!=0 and x!=7:
                #For non-edge cases:
                if x-1 not in xlist and x+1 not in xlist:
                    isolated+=1
            elif x==0 and 1 not in xlist:
                #Left edge:
                isolated+=1
            elif x==7 and 6 not in xlist:
                #Right edge:
                isolated+=1
        return isolated

#Initialize the board:

class Board:
    def __init__(self):
        self.create_board()

    def create_board(self):
        self.chess=[[0]*8 for i in range(8)]
        list_w=['Rw','Nw','Bw','Qw','Kw','Bw','Nw','Rw']
        list_b=['Rb','Nb','Bb','Qb','Kb','Bb','Nb','Rb']
        for i in range(2):
            for j in range (8):
                if i==0:
                    self.chess[i][j]=list_b[j]
                else:
                    self.chess[i][j]='Pb'
        for i in range(6,8):
            for j in range (8):
                if i==7:
                    self.chess[i][j]=list_w[j]
                else:
                    self.chess[i][j]='Pw'
    def getChess(self):
        return self.chess


class PieceTable:

    def __init__(self):

        self.pawn_table = [  0,  0,  0,  0,  0,  0,  0,  0,
        50, 50, 50, 50, 50, 50, 50, 50,
        10, 10, 20, 30, 30, 20, 10, 10,
         5,  5, 10, 25, 25, 10,  5,  5,
         0,  0,  0, 20, 20,  0,  0,  0,
         5, -5,-10,  0,  0,-10, -5,  5,
         5, 10, 10,-20,-20, 10, 10,  5,
         0,  0,  0,  0,  0,  0,  0,  0]

        self.knight_table = [-50,-40,-30,-30,-30,-30,-40,-50,
        -40,-20,  0,  0,  0,  0,-20,-40,
        -30,  0, 10, 15, 15, 10,  0,-30,
        -30,  5, 15, 20, 20, 15,  5,-30,
        -30,  0, 15, 20, 20, 15,  0,-30,
        -30,  5, 10, 15, 15, 10,  5,-30,
        -40,-20,  0,  5,  5,  0,-20,-40,
        -50,-90,-30,-30,-30,-30,-90,-50]

        self.bishop_table = [-20,-10,-10,-10,-10,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -10,  0,  5, 10, 10,  5,  0,-10,
        -10,  5,  5, 10, 10,  5,  5,-10,
        -10,  0, 10, 10, 10, 10,  0,-10,
        -10, 10, 10, 10, 10, 10, 10,-10,
        -10,  5,  0,  0,  0,  0,  5,-10,
        -20,-10,-90,-10,-10,-90,-10,-20]

        self.rook_table = [0,  0,  0,  0,  0,  0,  0,  0,
          5, 10, 10, 10, 10, 10, 10,  5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
         -5,  0,  0,  0,  0,  0,  0, -5,
          0,  0,  0,  5,  5,  0,  0,  0]

        self.queen_table = [-20,-10,-10, -5, -5,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -10,  0,  5,  5,  5,  5,  0,-10,
         -5,  0,  5,  5,  5,  5,  0, -5,
          0,  0,  5,  5,  5,  5,  0, -5,
        -10,  5,  5,  5,  5,  5,  0,-10,
        -10,  0,  5,  0,  0,  0,  0,-10,
        -20,-10,-10, 70, -5,-10,-10,-20]

        self.king_table = [-30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -20,-30,-30,-40,-40,-30,-30,-20,
        -10,-20,-20,-20,-20,-20,-20,-10,
         20, 20,  0,  0,  0,  0, 20, 20,
         20, 30, 10,  0,  0, 10, 30, 20]

        self.king_endgame_table = [-50,-40,-30,-20,-20,-30,-40,-50,
        -30,-20,-10,  0,  0,-10,-20,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-30,  0,  0,  0,  0,-30,-30,
        -50,-30,-30,-30,-30,-30,-30,-50]


##############################////////GUI FUNCTIONS\\\\\\\\\\\\\#############################
#########MAIN FUNCTION####################################################
class GUI:

    def __init__(self):
        self.board = Board().getChess()
        self.c = Commands()
        self.a = AI()
        #In chess some data must be stored that is not apparent in the board:
        self.player = 0 #This is the player that makes the next move. 0 is white, 1 is black
        self.castling_rights = [[True, True],[True, True]]
        #The above stores whether or not each of the players are permitted to castle on
        #either side of the king. (Kingside, Queenside)
        self.En_Passant_Target = -1 #This variable will store a coordinate if there is a square that can be
                               #en passant captured on. Otherwise it stores -1, indicating lack of en passant
                               #targets.
        self.half_move_clock = 0 #This variable stores the number of reversible moves that have been played so far.
        #Generate an instance of GamePosition class to store the above data:
        self.position = GamePosition(self.board,self.player,self.castling_rights,self.En_Passant_Target
                                ,self.half_move_clock)

        #Store the piece square tables here so they can be accessed globally by pieceSquareTable() function:

        pygame.init()

        self.size = (640, 640)
        self.screen = pygame.display.set_mode(self.size)
        pygame.display.set_caption("Chess Game                                                          Press *e* to Exit")
        self.game_icon = pygame.image.load('newMedia/ChessImage.png')
        pygame.display.set_icon(self.game_icon)

        self.media()

        self.bg = (49, 60, 43)

        self.startPage = pygame.Surface(self.size)
        self.startPage.fill(self.bg)

        self.diffPage = pygame.Surface(self.size)
        self.diffPage.fill(self.bg)

        self.flipPage = pygame.Surface(self.size)
        self.flipPage.fill(self.bg)

        self.selectPage = pygame.Surface(self.size)
        self.selectPage.fill(self.bg)

        self.colorPage = pygame.Surface(self.size)
        self.colorPage.fill(self.bg)

        # Stored [ x , y , width , height ] of buttons
        self.buttons = {
            1: [460-275, 380-15, 280, 75],
            2: [460-275, 470-15, 280, 75],
            3: [325-275, 280-15, 250, 250],
            4: [625-275, 280-15, 250, 250],
            5: [309-275, 250-15, 180, 180],
            6: [509-275, 250-15, 180, 180],
            7: [709-275, 250-15, 180, 180],
            8: [460-275, 560-15, 280, 75]
        }

        self.diffMenu = -1
        self.select = -1
        self.level = None
        self.temp = None

        self.box = pygame.image.load('newMedia/box.png')
        self.box = pygame.transform.scale(self.box, (640, 640))

        self.screen.blit(self.box,(0,0))
        pygame.mixer.Sound.play(self.welcome_sound)
        clock = pygame.time.Clock()  # Helps controlling fps of the game.
        self.initialize()
        pygame.display.update()

        #########################INFINITE LOOP#####################################
        #The program remains in this loop until the user quits the application
        while not self.gameEnded:
            if self.isMenu:
                #Menu needs to be shown right now.
                #Blit the background:
                #self.screen.blit(self.background,(0,0))         
                if self.isAI==-1:
                    self.startMenu()
                elif self.isAI==True:
                    if self.diffMenu == -1:
                        self.play1Menu_A()
                    elif self.diffMenu == 1:
                        self.play1Menu_B()
                    if self.select == 1 and self.temp == None:
                        self.selectMenu()
                elif self.isAI==False:
                    self.selectMenu()
                if self.isFlip!=-1 and self.select == 2 :
                    self.call_board()
                    continue
                elif self.isFlip!=-1 and self.select == 3 :
                    self.call_board()
                    pygame.mixer.Sound.play(self.instructions_sound)
                    continue
                if self.isFlip!=-1 and self.temp == -1 :
                    self.call_board()
                    continue
                for event in pygame.event.get():
                    #Handle the events while in menu:
                    if event.type == KEYDOWN:
                        if event.key == K_e :
                            self.gameEnded = True
                    elif event.type == QUIT:
                        self.gameEnded = True
                        #Window was closed.
                        #self.gameEnded = True
                        pygame.mixer.Sound.play(self.exit_sound)
                        break
                    if event.type == MOUSEBUTTONUP:
                        self.onClick()

                #Update the display:
                pygame.display.update()

                #Run at specific fps:
                clock.tick(10)
                continue
            #Menu part was done if this part reached.
            #If the AI is currently thinking the move to play
            #next, show some fancy looking squares to indicate
            #that.
            #Do it every 6 frames so it's not too fast:
            self.numm+=1
            if self.isAIThink and self.numm%10==0:
                self.Thinking()

            for event in pygame.event.get():
                #Deal with all the user inputs:
                if event.type == KEYDOWN:
                    if event.key == K_e:
                        self.gameEnded = True
                    #Window was closed.
                    elif event.type == QUIT:
                        self.gameEnded = True
                    #self.gameEnded = True
                    pygame.mixer.Sound.play(self.exit_sound)
                    break
                #Under the following conditions, user input should be
                #completely ignored:
                if self.chessEnded or self.isTransition or self.isAIThink:
                    continue
                #isDown means a piece is being dragged.
                if self.select<=2:
                    if not self.isDown and event.type == MOUSEBUTTONDOWN:
                        #Mouse was pressed down.
                        #Get the oordinates of the mouse
                        pos = pygame.mouse.get_pos()
                        if pos[0] in range(0,640) and pos[1] in range(0,640):
                        #convert to chess coordinates:
                            chess_coord = self.pixel_coord_to_chess(pos)
                            x = chess_coord[0]
                            y = chess_coord[1]
                            #If the piece clicked on is not occupied by your own piece,
                            #ignore this mouse click:
                            if not self.c.isOccupiedby(self.board,x,y,'wb'[self.player]):

                                continue
                            #Now we're sure the user is holding their mouse on a
                            #piecec that is theirs.
                            #Get reference to the piece that should be dragged around or selected:
                            dragPiece = self.getPiece(chess_coord)
                            #Find the possible squares that this piece could attack:
                            listofTuples = self.c.findPossibleSquares(self.position,x,y)
                            #Highlight all such squares:
                            self.createShades(listofTuples)
                            #A green box should appear on the square which was selected, unless
                            #it's a king under check, in which case it shouldn't because the king

                            #has a red color on it in that case.
                            if dragPiece:
                                if ((dragPiece.pieceinfo[0]=='K') and
                                    (self.c.isCheck(self.position,'white') or self.c.isCheck(self.position,'black'))):
                                    None
                                else:
                                    self.listofShades.append(Shades(self.greenbox_image,(x,y)))
                                #A piece is being dragged:
                            self.isDown = True
                    if (self.isDown or self.isClicked) and event.type == MOUSEBUTTONUP:
                        #Mouse was released.
                        self.isDown = False
                        #Snap the piece back to its coordinate position
                        if dragPiece:
                            dragPiece.setpos((-1,-1))
                        #Get coordinates and convert them:
                        pos = pygame.mouse.get_pos()
                        chess_coord = self.pixel_coord_to_chess(pos)
                        x2 = chess_coord[0]
                        y2 = chess_coord[1]
                        #Initialize:
                        self.isTransition = False
                        if (x,y)==(x2,y2): #NO dragging occured
                            #(ie the mouse was held and released on the same square)
                            if not self.isClicked: #nothing had been clicked previously
                                #This is the first click
                                self.isClicked = True
                                self.prevPos = (x,y) #Store it so next time we know the origin
                            else: #Something had been clicked previously
                                #Find out location of previous click:
                                x,y = self.prevPos
                                if (x,y)==(x2,y2): #User clicked on the same square again.
                                    #So
                                    self.isClicked = False
                                    #Destroy all shades:
                                    window = Tk()
                                    window.wm_withdraw()

                                    window.geometry("1x1+200+200")
                                    tkinter.messagebox.showinfo(title="Invalid move",message="Invalid move",parent=window)


                                else:
                                    #User clicked elsewhere on this second click:
                                    if self.c.isOccupiedby(self.board,x2,y2,'wb'[self.player]):
                                        #User clicked on a square that is occupied by their
                                        #own piece.
                                        #This is like making a first click on your own piece:
                                        self.isClicked = True
                                        self.prevPos = (x2,y2) #Store it
                                    else:
                                        #The user may or may not have clicked on a valid target square.
                                        self.isClicked = False
                                        #Destory all shades
                                        if not (x2,y2) in listofTuples:
                                            window = Tk()
                                            window.wm_withdraw()

                                            window.geometry("1x1+200+200")
                                            tkinter.messagebox.showinfo(title="Invalid move",message="Invalid move",parent=window)


                        if not (x2,y2) in listofTuples:
                            #Move was invalid
                            self.isTransition = False
                            continue
                        #Reaching here means a valid move was selected.
                        #If the recording option was selected, store the move to the opening dictionary:
                        if self.isRecord:
                            key = self.c.pos2key(self.position)
                            #Make sure it isn't already in there:
                            if [(x,y),(x2,y2)] not in self.openings[key]:
                                self.openings[key].append([(x,y),(x2,y2)])

                        #Make the move:
                        self.c.makemove(self.position,x,y,x2,y2)
                        #Update this move to be the 'previous' move (latest move in fact), so that
                        #yellow shades can be shown on it.
                        self.prevMove = [x,y,x2,y2]
                        #Update which player is next to play:
                        self.player = self.position.getplayer()
                        if self.player == 1:
                            pygame.mixer.Sound.play(self.piece_sound)
                        else:
                            pygame.mixer.Sound.play(self.piece_sound)
                        #Add the new position to the history for it:
                        self.position.addtoHistory(self.position)
                        #Check for possibilty of draw:
                        HMC = self.position.getHMC()
                        if HMC>=100 or self.c.isStalemate(self.position) or self.position.checkRepition():
                            #There is a draw:
                            self.isDraw = True
                            self.chessEnded = True
                        #Check for possibilty of checkmate:
                        if self.c.isCheckmate(self.position,'white'):
                            self.winner = 'b'
                            self.chessEnded = True
                        if self.c.isCheckmate(self.position,'black'):
                            self.winner = 'w'
                            self.chessEnded = True
                        #If the AI option was selected and the game still hasn't finished,
                        #let the AI start thinking about its next move:
                        if self.isAI and not self.chessEnded:
                            if self.player==0:
                                colorsign = 1
                            else:
                                colorsign = -1
                            self.bestMoveReturn = []
                            self.move_thread = threading.Thread(target = self.a.negamax,
                                        args = (self.position,self.level,-1000000,1000000,colorsign,self.bestMoveReturn,self.openings,self.searched))
                            self.move_thread.start()
                            self.isAIThink = True

                        #Move the piece to its new destination:
                        dragPiece.setcoord((x2,y2))
                        #There may have been a capture, so the piece list should be regenerated.
                        #However, if animation is ocurring, the the captured piece should still remain visible.
                        if not self.isTransition:
                            self.listofWhitePieces,self.listofBlackPieces = self.createPieces(self.board)
                        else:
                            movingPiece = dragPiece
                            origin = self.chess_coord_to_pixels((x,y))
                            print("Source     :",(y,x))
                            destiny = self.chess_coord_to_pixels((x2,y2))
                            print("Destination:",(y2,x2))
                            print("\n")
                            movingPiece.setpos(origin)
                            step = (destiny[0]-origin[0],destiny[1]-origin[1])

                        #Either way shades should be deleted now:
                        self.createShades([])
                else:
                    if event.type == pygame.MOUSEBUTTONDOWN and event.button==1:
                        if self.player==1:
                            self.letters_dict = {'a': 7, 'b': 6, 'c': 5, 'd': 4, 'e': 3, 'f': 2, 'g': 1, 'h': 0}
                            self.numbers_dict = {'1': 0, '2': 1, '3': 2, '4': 3, '5': 4, '6': 5, '7': 6, '8': 7}
                        with sr.Microphone() as source:
                            self.r.adjust_for_ambient_noise(source)
                            pygame.mixer.Sound.play(self.selectpiece_sound)
                            time.sleep(1.5)
                            try:
                                audio = self.r.listen(source,timeout=2,phrase_time_limit=2)
                                print("Recognizing...")
                                query = self.r.recognize_google(audio)
                                print(f"User said: {query}\n")
                                voice = query.lower()
                                if voice=='avon' or voice=='ye one' or voice=='evan' or voice=='yah 1':
                                    voice='a1'
                                elif voice == 'heetu' or voice=='hetu' or voice=='do' or voice =='tattoo' or voice =='airport' or voice =='tetu' or voice =='edu':
                                    voice='a2'
                                elif voice == 'a tree' or voice=='83' or voice=='yatri':
                                    voice='a3'
                                elif voice == 'krrish 4':
                                    voice='a4'
                                elif voice=='before':
                                    voice='b4'
                                elif voice=='bittu' or voice=='titu':
                                    voice='b2'
                                elif voice=='ba' or voice=='b.ed':
                                    voice='b8'
                                elif voice=='shivan' or voice=='shiva' or voice=='civil':
                                    voice='c1'
                                elif voice=='ceat':
                                    voice='c8'
                                elif voice=='deewan' or voice=='d 1' or voice=='devon' or voice=='devil':
                                    voice='d1'
                                elif voice=='even' or voice=='evil' or voice=='evan' or voice=='yuvan' or voice=='t1':
                                    voice='e1'
                                elif voice=='youtube' or voice=='tu':
                                    voice='e2'
                                elif voice=='mi 4':
                                    voice='e4'
                                elif voice=='mi 5':
                                    voice='e5'
                                elif voice=='8':
                                    voice='e8'
                                elif voice=='jivan':
                                    voice='g1'
                                elif voice=='jeetu' or voice=='jitu':
                                    voice='g2'
                                elif voice=='zefo':
                                    voice='g4'
                                elif voice=='quit' or voice =='end' or voice == 'close' or voice=='stop' or voice=='friend' or voice=='top' or voice=='finish' or voice=='and':
                                    pygame.mixer.Sound.play(self.exit_sound)
                                    self.gameEnded=True
                                if len(voice) == 2:
                                    letter = voice[0]
                                    number = voice[1]
                                    if letter=='v':
                                        letter='b'
                                    elif letter=='s':
                                        letter='h'
                                    if letter in self.letters_dict.keys() and number in self.numbers_dict.keys():
                                        print(self.letters_dict[letter], self.numbers_dict[number])
                                        chess_coord = (self.letters_dict[letter], self.numbers_dict[number])
                                        x = chess_coord[0]
                                        y = chess_coord[1]
                                        # If the piece clicked on is not occupied by your own piece,
                                        # ignore this mouse click:
                                        if not self.c.isOccupiedby(self.board, x, y, 'wb'[self.player]):
                                            continue
                                        # Now we're sure the user is holding their mouse on a
                                        # piecec that is theirs.
                                        # Get reference to the piece that should be dragged around or selected:
                                        dragPiece = self.getPiece(chess_coord)
                                        # Find the possible squares that this piece could attack:
                                        listofTuples = self.c.findPossibleSquares(self.position, x, y)
                                        # Highlight all such squares:
                                        self.createShades(listofTuples)
                                        # A green box should appear on the square which was selected, unless
                                        # it's a king under check, in which case it shouldn't because the king
                                        # has a red color on it in that case.
                                        if dragPiece:
                                            if ((dragPiece.pieceinfo[0] == 'K') and
                                                    (self.c.isCheck(self.position, 'white') or self.c.isCheck(self.position,
                                                                                                              'black'))):
                                                None
                                            else:
                                                self.listofShades.append(Shades(self.greenbox_image, (x, y)))
                                        self.piece_selected_by_voice = True
                            except sr.UnknownValueError:
                                pygame.mixer.Sound.play(self.repeat_sound)
                            except sr.RequestError:
                                pygame.mixer.Sound.play(self.requesterror_sound)
                            except Exception:
                                pygame.mixer.Sound.play(self.repeat_sound)


                    #Move to Destination Using voice
                    elif self.piece_selected_by_voice and event.type==pygame.MOUSEBUTTONDOWN and event.button==3 :
                        self.piece_selected_by_voice = False
                        with sr.Microphone() as source:
                            while True:
                                self.r.adjust_for_ambient_noise(source)
                                pygame.mixer.Sound.play(self.destination_sound)
                                time.sleep(1.5)
                                try:
                                    audio = self.r.listen(source,timeout=2,phrase_time_limit=2)
                                    print("Recognizing...")
                                    query2 = self.r.recognize_google(audio)
                                    print(f"User said: {query2}\n")
                                    voice2 = query2.lower()
                                    if voice2=='avon':
                                        voice2='a1'
                                    elif voice2 == 'heetu' or voice2=='hetu' or voice2=='do' or voice2 =='tattoo' or voice2 =='airport' or voice2 =='tetu' or voice2 =='edu':
                                        voice2='a2'
                                    elif voice2 == 'a tree' or voice2=='83':
                                        voice2='a3'
                                    elif voice2 == 'krrish 4':
                                        voice2='a4'
                                    elif voice2=='before':
                                        voice2='b4'
                                    elif voice2=='bittu' or voice2=='titu':
                                        voice2='b2'
                                    elif voice2=='ba' or voice2=='b.ed':
                                        voice2='b8'
                                    elif voice2=='shivan' or voice2=='shiva' or voice2=='civil':
                                        voice2='c1'
                                    elif voice2=='ceat':
                                        voice2='c8'
                                    elif voice2=='deewan' or voice2=='d 1' or voice2=='devon' or voice2=='devil':
                                        voice2='d1'
                                    elif voice2=='even' or voice2=='evil' or voice2=='evan' or voice2=='yuvan' or voice2=='t1':
                                        voice='e1'
                                    elif voice2=='youtube' or voice2=='tu':
                                        voice2='e2'
                                    elif voice2=='mi 4':
                                        voice2='e4'
                                    elif voice2=='mi 5':
                                        voice2='e5'
                                    elif voice2=='8':
                                        voice2='e8'
                                    elif voice2=='jivan':
                                        voice2='g1'
                                    elif voice2=='jeetu' or voice2=='jitu':
                                        voice2='g2'
                                    elif voice2=='zefo':
                                        voice2='g4'
                                    elif voice2 == 'quit' or voice2 == 'end' or voice2 == 'close' or voice2=='stop' or voice2=='friend' or voice2=='top' or voice2=='finish' or voice2=='and':
                                        pygame.mixer.Sound.play(self.exit_sound)
                                        self.gameEnded=True
                                        break
                                    if len(voice2) == 2:
                                        letter = voice2[0]
                                        number = voice2[1]
                                        if letter=='v':
                                            letter='b'
                                        elif letter=='s':
                                            letter='h'
                                        if letter in self.letters_dict.keys() and number in self.numbers_dict.keys():
                                            print(self.letters_dict[letter], self.numbers_dict[number])
                                            chess_coord = (self.letters_dict[letter], self.numbers_dict[number])
                                            x2 = chess_coord[0]
                                            y2 = chess_coord[1]
                                            # Initialize:
                                            self.isTransition = False
                                            if not (x2, y2) in listofTuples:
                                                # Move was invalid
                                                self.isTransition = False
                                                pygame.mixer.Sound.play(self.invalid_sound)

                                                continue
                                            # Reaching here means a valid move was selected.
                                            # If the recording option was selected, store the move to the opening dictionary:
                                            if self.isRecord:
                                                key = self.c.pos2key(self.position)
                                                # Make sure it isn't already in there:
                                                if [(x, y), (x2, y2)] not in self.openings[key]:
                                                    self.openings[key].append([(x, y), (x2, y2)])

                                            # Make the move:
                                            self.c.makemove(self.position, x, y, x2, y2)
                                            # Update this move to be the 'previous' move (latest move in fact), so that
                                            # yellow shades can be shown on it.
                                            self.prevMove = [x, y, x2, y2]
                                            # Update which player is next to play:
                                            self.player = self.position.getplayer()
                                            if self.player == 1:
                                                pygame.mixer.Sound.play(self.piece_sound)
                                            else:
                                                pygame.mixer.Sound.play(self.piece_sound)
                                            # Add the new position to the history for it:
                                            self.position.addtoHistory(self.position)
                                            # Check for possibilty of draw:
                                            HMC = self.position.getHMC()
                                            if HMC >= 100 or self.c.isStalemate(self.position) or self.position.checkRepition():
                                                # There is a draw:
                                                self.isDraw = True
                                                self.chessEnded = True
                                            # Check for possibilty of checkmate:
                                            if self.c.isCheckmate(self.position, 'white'):
                                                self.winner = 'b'
                                                self.chessEnded = True
                                            if self.c.isCheckmate(self.position, 'black'):
                                                self.winner = 'w'
                                                self.chessEnded = True
                                            # If the AI option was selected and the game still hasn't finished,
                                            # let the AI start thinking about its next move:
                                            if self.isAI and not self.chessEnded:
                                                if self.player == 0:
                                                    colorsign = 1
                                                else:
                                                    colorsign = -1
                                                self.bestMoveReturn = []
                                                self.move_thread = threading.Thread(target=self.a.negamax,
                                                                                    args=(self.position, self.level, -1000000, 1000000,
                                                                                          colorsign,
                                                                                          self.bestMoveReturn, self.openings,
                                                                                          self.searched))
                                                self.move_thread.start()
                                                self.isAIThink = True

                                            # Move the piece to its new destination:
                                            dragPiece.setcoord((x2, y2))
                                            # There may have been a capture, so the piece list should be regenerated.
                                            # However, if animation is ocurring, the the captured piece should still remain visible.
                                            if not self.isTransition:
                                                self.listofWhitePieces, self.listofBlackPieces = self.createPieces(self.board)
                                            else:
                                                movingPiece = dragPiece
                                                origin = self.chess_coord_to_pixels((x, y))
                                                destiny = self.chess_coord_to_pixels((x2, y2))
                                                movingPiece.setpos(origin)
                                                step = (destiny[0] - origin[0], destiny[1] - origin[1])

                                            # Either way shades should be deleted now:
                                            self.createShades([])
                                            break

                                except sr.UnknownValueError:
                                    pygame.mixer.Sound.play(self.repeat_sound)
                                except sr.RequestError:
                                    pygame.mixer.Sound.play(self.requesterror_sound)
                                except Exception:
                                    pygame.mixer.Sound.play(self.repeat_sound)



            #If an animation is supposed to happen, make it happen:
            if self.isTransition:
                p,q = movingPiece.getpos()
                dx2,dy2 = destiny
                n= 30.0
                if abs(p-dx2)<=abs(step[0]/n) and abs(q-dy2)<=abs(step[1]/n):
                    #The moving piece has reached its destination:
                    #Snap it back to its grid position:
                    movingPiece.setpos((-1,-1))
                    #Generate new piece list in case one got captured:
                    self.listofWhitePieces,self.listofBlackPieces = self.createPieces(self.board)
                    #No more transitioning:
                    self.isTransition = False
                    self.createShades([])
                else:
                    #Move it closer to its destination.
                    movingPiece.setpos((p+step[0]/n,q+step[1]/n))
            #If a piece is being dragged let the dragging piece follow the mouse:
            if self.isDown:
                m,k = pygame.mouse.get_pos()
                if dragPiece:
                    dragPiece.setpos((m-self.square_width/2,k-self.square_height/2))
            #If the AI is thinking, make sure to check if it isn't done thinking yet.
            #Also, if a piece is currently being animated don't ask the AI if it's
            #done thining, in case it replied in the affirmative and starts moving
            #at the same time as your piece is moving:
            if self.isAIThink and not self.isTransition:
                if not self.move_thread.is_alive():
                    #The AI has made a decision.
                    #It's no longer thinking
                    self.isAIThink = False
                    #Destroy any shades:
                    self.createShades([])
                    #Get the move proposed:
                    if len(self.bestMoveReturn)==2:
                        [x,y],[x2,y2] = self.bestMoveReturn
                    else:
                        self.c.allMoves(self.position,color)
                    #Do everything just as if the user made a move by click-click movement:
                    self.c.makemove(self.position,x,y,x2,y2)
                    self.prevMove = [x,y,x2,y2]
                    self.player = self.position.getplayer()
                    HMC = self.position.getHMC()
                    self.position.addtoHistory(self.position)
                    if HMC>=100 or self.c.isStalemate(self.position) or self.position.checkRepition():
                        self.isDraw = True
                        self.chessEnded = True
                    if self.c.isCheckmate(self.position,'white'):
                        self.winner = 'b'
                        self.chessEnded = True
                    if self.c.isCheckmate(self.position,'black'):
                        self.winner = 'w'
                        self.chessEnded = True
                    #Animate the movement:
                    self.isTransition = True
                    movingPiece = self.getPiece((x,y))
                    origin = self.chess_coord_to_pixels((x,y))
                    destiny = self.chess_coord_to_pixels((x2,y2))
                    movingPiece.setpos(origin)
                    step = (destiny[0]-origin[0],destiny[1]-origin[1])
                    pygame.mixer.Sound.play(self.piece_sound)
            #Update positions of all images:
            self.drawBoard()
            #Update the display:
            pygame.display.update()

            #Run at specific fps:
            clock.tick(60)

        #Out of loop. Quit pygame:
        time.sleep(2)
        pygame.quit()
        #In case recording mode was on, save the openings dictionary to a file:
        if self.isRecord:
            file_handle.seek(0)
            pickle.dump(self.openings,file_handle)
            file_handle.truncate()
            file_handle.close()

    def DisplayPage(self, pageName):
        self.SurfacesAtTop = self.SurfacesAtTop.fromkeys(self.SurfacesAtTop, False)
        self.screen.blit(self.Surfaces[pageName], (0, 0))
        self.SurfacesAtTop[pageName] = True

    def chess_coord_to_pixels(self,chess_coord):
        x,y = chess_coord

        #There are two sets of coordinates that this function could choose to return.
        #One is the coordinates that would be usually returned, the other is one that
        #would be returned if the board were to be flipped.
        #Note that square width and height variables are defined in the main function and
        #so are accessible here as global variables.

        if self.isAI:
            if self.AIPlayer==0:
                #This means you're playing against the AI and are playing as black:
                return ((7-x)*self.square_width, (7-y)*self.square_height)
            else:
                return (x*self.square_width, y*self.square_height)
        #Being here means two player game is being played.
        #If the flipping mode is enabled, and the player to play is black,
        #the board should flip, but not until the transition animation for
        #white movement is complete:

        if not self.isFlip or self.player==0 ^ self.isTransition:
            return (x*self.square_width, y*self.square_height)
        else:
            return ((7-x)*self.square_width, (7-y)*self.square_height)
    def pixel_coord_to_chess(self,pixel_coord):
        if pixel_coord[0] in range(0,640) and pixel_coord[1] in range(0,640):
            x,y = (pixel_coord[0])//self.square_width, (pixel_coord[1])//self.square_height

            #See comments for chess_coord_to_pixels() for an explanation of the
            #conditions seen here:

            if self.isAI:
                if self.AIPlayer==0:
                    return (7-x,7-y)
                else:
                    return (x,y)
            if not self.isFlip or self.player==0 ^ self.isTransition:
                return (x,y)
            else:
                return (7-x,7-y)
    def getPiece(self,chess_coord):
        for piece in self.listofWhitePieces+self.listofBlackPieces:

            #piece.getInfo()[0] represents the chess coordinate occupied
            #by piece.

            if piece.getInfo()[0] == chess_coord:
                return piece
    def createPieces(self,board):
        #Initialize containers:
        self.listofWhitePieces = []
        self.listofBlackPieces = []
        #Loop through all squares:
        for i in range(8):
            for k in range(8):
                if board[i][k]!=0:
                    #The square is not empty, create a piece object:
                    p = Piece(board[i][k],(k,i), self.square_width, self.square_height)
                    #Append the reference to the object to the appropriate
                    #list:
                    if board[i][k][1]=='w':
                        self.listofWhitePieces.append(p)
                    else:
                        self.listofBlackPieces.append(p)
        #Return both:
        return [self.listofWhitePieces,self.listofBlackPieces]
    def createShades(self,listofTuples):


        #Empty the list
        self.listofShades = []
        if self.isTransition:
            #Nothing should be shaded when a piece is being animated:
            return
        if self.isDraw:
            #The game ended with a draw. Make yellow circle shades for
            #both the kings to show this is the case:

            coord = self.c.lookfor(self.board,'Kw')[0]
            shade = Shades(self.circle_image_yellow,coord)
            self.listofShades.append(shade)
            coord = self.c.lookfor(self.board,'Kb')[0]
            shade = Shades(self.circle_image_yellow,coord)
            self.listofShades.append(shade)
            pygame.mixer.Sound.play(self.draw_sound)
            #There is no need to go further:
            return
        if self.chessEnded:

            #The game has ended, with a checkmate because it cannot be a
            #draw if the code reached here.
            #Give the winning king a green circle shade:

            coord = self.c.lookfor(self.board,'K'+self.winner)[0]
            shade = Shades(self.circle_image_green_big,coord)
            self.listofShades.append(shade)
            if self.winner=='w':
                pygame.mixer.Sound.play(self.whitewin_sound)
            else:
                pygame.mixer.Sound.play(self.blackwin_sound)

        #If either king is under attack, give them a red circle:

        if self.c.isCheck(self.position,'white'):
            coord = self.c.lookfor(self.board,'Kw')[0]
            shade = Shades(self.circle_image_red,coord)
            self.listofShades.append(shade)
            pygame.mixer.Sound.play(self.checkmate_sound)
        if self.c.isCheck(self.position,'black'):
            coord = self.c.lookfor(self.board,'Kb')[0]
            shade = Shades(self.circle_image_red,coord)
            self.listofShades.append(shade)
            pygame.mixer.Sound.play(self.checkmate_sound)
        #Go through all the target squares inputted:
        for pos in listofTuples:
            #If the target square is occupied, it can be captured.
            #For a capturable square, there is a different shade.
            #Create the appropriate shade for each target square:
            if self.c.isOccupied(self.board,pos[0],pos[1]):
                img = self.circle_image_capture
            else:
                img = self.circle_image_green
            shade = Shades(img,pos)
            #Append:
            self.listofShades.append(shade)
    def drawBoard(self):
        #Blit the background:
        self.screen.blit(self.background,(0,0))

        #Choose the order in which to blit the pieces.
        #If black is about to play for example, white pieces
        #should be blitted first, so that when black is capturing,
        #the piece appears above:

        if self.player==1:
            order = [self.listofWhitePieces,self.listofBlackPieces]
        else:
            order = [self.listofBlackPieces,self.listofWhitePieces]
        if self.isTransition:
            #If a piece is being animated, the player info is changed despite
            #white still capturing over black, for example. Reverse the order:
            order = list(reversed(order))

        #The shades which appear during the following three conditions need to be
        #blitted first to appear under the pieces:

        if self.isDraw or self.chessEnded or self.isAIThink:
            #Shades
            for shade in self.listofShades:
                img,chess_coord = shade.getInfo()
                pixel_coord = self.chess_coord_to_pixels(chess_coord)
                self.screen.blit(img,pixel_coord)

        #Make shades to show what the previous move played was:
        if self.prevMove[0]!=-1 and not self.isTransition:
            x,y,x2,y2 = self.prevMove
            self.screen.blit(self.yellowbox_image,self.chess_coord_to_pixels((x,y)))
            self.screen.blit(self.yellowbox_image,self.chess_coord_to_pixels((x2,y2)))

        #Blit the Pieces:
        #Notw that one side has to be below the green circular shades to show
        #that they are being targeted, and the other side if dragged to such
        # a square should be blitted on top to show that it is capturing:

        #Potentially captured pieces:
        for piece in order[0]:

            chess_coord,subsection,pos = piece.getInfo()
            pixel_coord = self.chess_coord_to_pixels(chess_coord)
            if pos==(-1,-1):
                #Blit to default square:
                self.screen.blit(self.pieces_image,pixel_coord,subsection)
            else:
                #Blit to the specific coordinates:
                self.screen.blit(self.pieces_image,pos,subsection)

        #Blit the shades in between:
        if not (self.isDraw or self.chessEnded or self.isAIThink):
            for shade in self.listofShades:
                img,chess_coord = shade.getInfo()
                pixel_coord = self.chess_coord_to_pixels(chess_coord)
                self.screen.blit(img,pixel_coord)

        #Potentially capturing pieces:
        for piece in order[1]:
            chess_coord,subsection,pos = piece.getInfo()
            pixel_coord = self.chess_coord_to_pixels(chess_coord)
            if pos==(-1,-1):
                #Default square
                self.screen.blit(self.pieces_image,pixel_coord,subsection)
            else:
                #Specifc pixels:
                self.screen.blit(self.pieces_image,pos,subsection)

    def media(self):

        #Load all the images:
        #Load the background chess board image:
        self.background = pygame.image.load('Media\\board2.png').convert()

        #Load an image with all the pieces on it:
        pieces_image = pygame.image.load('Media\\Chess_Pieces_Sprite.png').convert_alpha()
        circle_image_green = pygame.image.load('Media\\green_circle_small.png').convert_alpha()
        circle_image_capture = pygame.image.load('Media\\green_circle_neg.png').convert_alpha()
        circle_image_red = pygame.image.load('Media\\red_circle_big.png').convert_alpha()
        greenbox_image = pygame.image.load('Media\\green_box.png').convert_alpha()
        circle_image_yellow = pygame.image.load('Media\\yellow_circle_big.png').convert_alpha()
        circle_image_green_big = pygame.image.load('Media\\green_circle_big.png').convert_alpha()
        yellowbox_image = pygame.image.load('Media\\yellow_box.png').convert_alpha()

       
        #Getting sizes:
        #Get background size:
        self.size_of_bg = self.background.get_rect().size

        #Get size of the individual squares
        self.square_width = self.size_of_bg[0]//8
        self.square_height = self.size_of_bg[1]//8


        #Rescale the images so that each piece can fit in a square:

        self.pieces_image = pygame.transform.scale(pieces_image,
                                              (self.square_width*6,self.square_height*2))
        self.circle_image_green = pygame.transform.scale(circle_image_green,
                                              (self.square_width, self.square_height))
        self.circle_image_capture = pygame.transform.scale(circle_image_capture,
                                              (self.square_width, self.square_height))
        self.circle_image_red = pygame.transform.scale(circle_image_red,
                                              (self.square_width, self.square_height))
        self.greenbox_image = pygame.transform.scale(greenbox_image,
                                              (self.square_width, self.square_height))
        self.yellowbox_image = pygame.transform.scale(yellowbox_image,
                                              (self.square_width, self.square_height))
        self.circle_image_yellow = pygame.transform.scale(circle_image_yellow,
                                                     (self.square_width, self.square_height))
        self.circle_image_green_big = pygame.transform.scale(circle_image_green_big,
                                                     (self.square_width, self.square_height))
        

        #Loading Sounds
        self.welcome_sound = pygame.mixer.Sound("Voice\welcome.wav")
        self.exit_sound = pygame.mixer.Sound("Voice\exit.wav")
        self.flip_sound = pygame.mixer.Sound("Voice\Flip.wav")
        self.color_sound = pygame.mixer.Sound("Voice\color.wav")
        self.thinking_sound = pygame.mixer.Sound("Voice\Thinking.wav")
        self.difficulty_sound=pygame.mixer.Sound("Voice\difficulty.wav")
        self.turn_sound=pygame.mixer.Sound("Voice\Turn.wav")
        self.checkmate_sound = pygame.mixer.Sound("Voice\check.wav")
        self.draw_sound = pygame.mixer.Sound("Voice\draw.wav")
        self.whitewin_sound = pygame.mixer.Sound("Voice\whitewins.wav")
        self.blackwin_sound = pygame.mixer.Sound("Voice\Blackwins.wav")
        self.blackturn_sound = pygame.mixer.Sound("Voice\Blackturn.wav")
        self.whiteturn_sound = pygame.mixer.Sound("Voice\whiteturn.wav")
        self.piece_sound=pygame.mixer.Sound("Voice\piecehit.wav")
        self.destination_sound=pygame.mixer.Sound("Voice\destination.wav")
        self.instructions_sound = pygame.mixer.Sound("Voice\instructions.wav")
        self.repeat_sound = pygame.mixer.Sound("Voice\Repeat.wav")
        self.selectpiece_sound = pygame.mixer.Sound("Voice\selectpiece.wav")
        self.requesterror_sound = pygame.mixer.Sound("Voice\Requesterror.wav")
        self.control_sound = pygame.mixer.Sound("Voice\control.wav")
        self.invalid_sound = pygame.mixer.Sound("Voice\invalid.wav")



    def initialize(self):


        #Generate a list of pieces that should be drawn on the board:
        self.listofWhitePieces,self.listofBlackPieces = self.createPieces(self.board)

        #(the list contains references to objects of the class Piece)
        #Initialize a list of shades:
        self.listofShades = []
        self.isDown = False #Variable that shows if the mouse is being held down
                       #onto a piece
        self.isClicked = False #To keep track of whether a piece was clicked in order
        #to indicate intention to move by the user.
        self.isTransition = False #Keeps track of whether or not a piece is being animated.
        self.isDraw = False #Will store True if the game ended with a draw
        self.chessEnded = False #Will become True once the chess game ends by checkmate, stalemate, etc.
        self.isRecord = False #Set this to True if you want to record moves to the Opening Book. Do not
        #set this to True unless you're 100% sure of what you're doing. The program will never modify
        #this value.
        self.isAIThink = False #Stores whether or not the AI is calculating the best move to be played.
        # Initialize the opening book dictionary, and set its values to be lists by default:
        self.openings = defaultdict(list)
        #If openingTable.txt exists, read from it and load the opening moves to the local dictionary.
        #If it doesn't, create a new one to write to if Recording is enabled:
        try:
            file_handle = open('openingTable.txt','r')
            self.openings = pickle.loads(file_handle.read())
        except:
            if self.isRecord:
                file_handle = open('openingTable.txt','w')

        self.letters_dict = {'a': 0, 'b': 1, 'c': 2, 'd': 3, 'e': 4, 'f': 5, 'g': 6, 'h': 7}#dictionary for voice
        self.numbers_dict = {'1': 7, '2': 6, '3': 5, '4': 4, '5': 3, '6': 2, '7': 1, '8': 0}#dictionary for voice
        self.piece_selected_by_voice=False
        self.r = sr.Recognizer()#speechrecognition class object
        self.r.dynamic_energy_threshold = False
        self.r.energy_threshold = 400
        self.searched = {} #Global variable that allows negamax to keep track of nodes that have
        #already been evaluated.
        self.prevMove = [-1,-1,-1,-1] #Also a global varible that stores the last move played, to
        #allow drawBoard() to create Shades on the squares.
        #Initialize some more values:
        #For animating AI thinking graphics:
        self.ax,self.ay=0,0
        self.numm = 0
        #For showing the menu and keeping track of user choices:
        self.isMenu = True
        self.isAI = -1
        self.isFlip = -1
        self.AIPlayer = -1
        #Finally, a variable to keep false until the user wants to quit:
        self.gameEnded = False

    def startMenu(self):
        #The user has not selected between playing against the AI
        #or playing against a friend.
        #So allow them to choose between playing with a friend or the AI:

        self.boardImage = pygame.image.load('newMedia/ChessImage.png')
        self.boardImage = pygame.transform.scale(self.boardImage, (300, 300))
        self.player1 = pygame.image.load('newMedia/play1.png')
        self.player1 = pygame.transform.scale(self.player1, (280, 75))
        self.player2 = pygame.image.load('newMedia/play2.png')
        self.player2 = pygame.transform.scale(self.player2, (280, 75))
        self.exit = pygame.image.load('newMedia/exit.png')
        self.exit = pygame.transform.scale(self.exit, (280, 75))

        self.startPage.blit(self.box,(0,0))

        self.startPage.blit(self.boardImage, (450-275, 60-15))
        self.startPage.blit(self.player1, (460-275, 380-15))
        self.startPage.blit(self.player2, (460-275, 470-15))
        self.startPage.blit(self.exit, (460-275, 560-15))

        self.screen.blit(self.startPage, (0, 0))

    def play1Menu_A(self):
        #The user has selected to play against the AI.
        #Allow the user to play as white or black:
        #self.screen.blit(self.playwhite_pic,(0,self.square_height*2))
        #self.screen.blit(self.playblack_pic,(self.square_width*4,self.square_height*2))

        self.selectcolor = pygame.image.load('newMedia/selectColor.png')
        self.selectcolor = pygame.transform.scale(self.selectcolor, (350, 80))
        self.playasblack = pygame.image.load('newMedia/playBlack.png')
        self.playasblack = pygame.transform.scale(self.playasblack, (250, 250))
        self.playaswhite = pygame.image.load('newMedia/playWhite.png')
        self.playaswhite = pygame.transform.scale(self.playaswhite, (250, 250))

        self.colorPage.blit(self.box,(0,0))

        self.colorPage.blit(self.selectcolor, (425-275, 80-15))
        self.colorPage.blit(self.playasblack, (325-275, 280-15))
        self.colorPage.blit(self.playaswhite, (625-275, 280-15))

        self.screen.blit(self.colorPage, (0, 0))
        global play_sound
        if play_sound:
            play_sound = False
            pygame.mixer.Sound.play(self.color_sound)


    def play1Menu_B(self):
        #The user has selected to play against the AI.
        #Allow the user to play as white or black:
        #self.screen.blit(self.playwhite_pic,(0,self.square_height*2))
        #self.screen.blit(self.playblack_pic,(self.square_width*4,self.square_height*2))

        self.selectDifficulty = pygame.image.load('newMedia/selectDifficulty.png')
        self.selectDifficulty = pygame.transform.scale(self.selectDifficulty, (350, 80))
        self.Easy = pygame.image.load('newMedia/Easy.png')
        self.Easy = pygame.transform.scale(self.Easy, (180, 180))
        self.Medium = pygame.image.load('newMedia/Medium.png')
        self.Medium = pygame.transform.scale(self.Medium, (180, 180))
        self.Hard = pygame.image.load('newMedia/Hard.png')
        self.Hard = pygame.transform.scale(self.Hard, (180, 180))

        self.diffPage.blit(self.box,(0,0))

        self.diffPage.blit(self.selectDifficulty, (425-275, 80-15))
        self.diffPage.blit(self.Easy, (309-275, 250-15))
        self.diffPage.blit(self.Medium, (509-275, 250-15))
        self.diffPage.blit(self.Hard, (709-275, 250-15))

        self.screen.blit(self.diffPage, (0, 0))
        self.diffMenu = 0
        global play_sound
        if play_sound:
            play_sound = False
            pygame.mixer.Sound.play(self.difficulty_sound)

    def play2Menu(self):
        #The user has selected to play with a friend.
        #Allow choice of flipping the board or not flipping the board:
        #self.screen.blit(self.flipDisabled_pic,(0,self.square_height*2))
        #self.screen.blit(self.flipEnabled_pic,(self.square_width*4,self.square_height*2))
        self.selectflip = pygame.image.load('newMedia/Flip.png')
        self.selectflip = pygame.transform.scale(self.selectflip, (350, 80))
        self.enableflip = pygame.image.load('newMedia/enableFlip.png')
        self.enableflip = pygame.transform.scale(self.enableflip, (250, 250))
        self.disableflip = pygame.image.load('newMedia/disableFlip.png')
        self.disableflip = pygame.transform.scale(self.disableflip, (250, 250))

        self.flipPage.blit(self.box,(0,0))

        self.flipPage.blit(self.selectflip, (425-275, 80-15))
        self.flipPage.blit(self.enableflip, (325-275, 280-15))
        self.flipPage.blit(self.disableflip, (625-275, 280-15))

        self.screen.blit(self.flipPage, (0, 0))
        global play_sound
        if play_sound:
            play_sound = False
            pygame.mixer.Sound.play(self.flip_sound)

    def selectMenu(self):
        self.selectmode = pygame.image.load('newMedia/selectMode.png')
        self.selectmode = pygame.transform.scale(self.selectmode, (350, 80))
        self.bymouse = pygame.image.load('newMedia/controlMouse.png')
        self.bymouse = pygame.transform.scale(self.bymouse, (250, 250))
        self.byvoice = pygame.image.load('newMedia/controlVoice.png')
        self.byvoice = pygame.transform.scale(self.byvoice, (250, 250))

        self.selectPage.blit(self.box, (0, 0))

        self.selectPage.blit(self.selectmode, (425 - 275, 80 - 15))
        self.selectPage.blit(self.bymouse, (325 - 275, 280 - 15))
        self.selectPage.blit(self.byvoice, (625 - 275, 280 - 15))

        self.screen.blit(self.selectPage, (0, 0))
        global play_sound
        if play_sound:
            play_sound = False
            pygame.mixer.Sound.play(self.control_sound)

    def call_board(self):
        #All settings have already been specified.
        #Draw all the pieces onto the board:
        self.drawBoard()
        #Don't let the menu ever appear again:
        self.isMenu = False
        #In case the player chose to play against the AI and decided to
        #play as black, call upon the AI to make a move:
        if self.isAI and self.AIPlayer==0:
            colorsign=1
            self.bestMoveReturn = []
            self.move_thread = threading.Thread(target = self.a.negamax,
                        args = (self.position,self.level,-1000000,1000000,colorsign,self.bestMoveReturn,self.openings,self.searched))
            self.move_thread.start()
            self.isAIThink = True

        for event in pygame.event.get():
                    #Handle the events while in menu:
            if event.type == KEYDOWN:
                if event.key == K_e:
                    self.gameEnded = True
                elif event.type == QUIT:
                    self.gameEnded = True
                        #Window was closed.
                        #self.gameEnded = True
                    pygame.mixer.Sound.play(self.exit_sound)
                    break
                if event.type == MOUSEBUTTONUP:
                    self.onClick()


    def onClick(self):
        global play_sound
        #The mouse was clicked somewhere.
        #Get the coordinates of click:

        posx, posy = pygame.mouse.get_pos()

        if self.buttons[1][0] < posx < self.buttons[1][0] + self.buttons[1][2]:
            if self.buttons[1][1] < posy < self.buttons[1][1] + self.buttons[1][3] and self.isAI == -1 :
                self.isAI = True
                posx , posy = (0 , 0)

        if self.buttons[2][0] < posx < self.buttons[2][0] + self.buttons[2][2] :
            if self.buttons[2][1] < posy < self.buttons[2][1] + self.buttons[2][3] and self.isAI == -1:
                self.isAI = False
                posx, posy = (0, 0)

        if self.buttons[3][0] < posx < self.buttons[3][0] + self.buttons[3][2]:
            if self.buttons[3][1] < posy < self.buttons[3][1] + self.buttons[3][3]:
                if self.isAI == True:
                    if self.diffMenu == -1:
                        self.AIPlayer = 0
                        self.isFlip = False
                        self.diffMenu = 1
                        posx, posy = (0, 0)
                        play_sound=True
                    elif self.isAI == True and self.select == 1:
                        self.select = 2
                        self.temp = 1
                        posx, posy = (0, 0)
                        print("Mouse Operated")
                elif self.isAI == False:
                    self.isFlip = True
                    self.temp = -1
                    print("Mouse operated")
                    posx, posy = (0, 0)
        if self.buttons[4][0] < posx < self.buttons[4][0] + self.buttons[4][2]:
            if self.buttons[4][1] < posy < self.buttons[4][1] + self.buttons[4][3]:
                if self.isAI == True:
                    if self.diffMenu == -1:
                        self.AIPlayer = 1
                        self.isFlip = False
                        self.diffMenu = 1
                        posx, posy = (0, 0)
                        play_sound = True
                    elif self.isAI == True and self.select == 1:
                        self.select = 3
                        self.temp = 1
                        posx, posy = (0, 0)
                        print("Voice Operated")
                elif self.isAI == False and self.select == 1:
                    self.isFlip = True
                    self.select = 3
                    self.temp = 1
                    posx, posy = (0, 0)
                    print("voice Operated")

        if self.buttons[5][0] < posx < self.buttons[5][0] + self.buttons[5][2]:
            if self.buttons[5][1] < posy < self.buttons[5][1] + self.buttons[5][3]:
                self.level = 1
                self.select = 1
                posx, posy = (0, 0)
                play_sound = True

        if self.buttons[6][0] < posx < self.buttons[6][0] + self.buttons[6][2]:
            if self.buttons[6][1] < posy < self.buttons[6][1] + self.buttons[6][3]:
                self.level = 2
                self.select = 1
                posx, posy = (0, 0)
                play_sound = True

        if self.buttons[7][0] < posx < self.buttons[7][0] + self.buttons[7][2]:
            if self.buttons[7][1] < posy < self.buttons[7][1] + self.buttons[7][3]:
                self.level = 3
                self.select = 1
                posx, posy = (0, 0)
                play_sound = True

        if self.buttons[8][0] < posx < self.buttons[8][0] + self.buttons[8][2]:
            if self.buttons[8][1] < posy < self.buttons[8][1] + self.buttons[8][3]:
                self.gameEnded = True
                pygame.mixer.Sound.play(self.exit_sound)
                posx, posy = (0, 0)

    def Thinking(self):
        
        ####while AI is thinking we will cause some fancy movements on screen
        self.ax+=1
        if self.ax==8:
            self.ay+=1
            self.ax=0
        if self.ay==8:
            self.ax,self.ay=0,0
        if self.ax%4==0:
            self.createShades([])
        #If the AI is white, start from the opposite side (since the board is flipped)
        if self.AIPlayer==0:
            self.listofShades.append(Shades(self.greenbox_image,(7-self.ax,7-self.ay)))
        else:
            self.listofShades.append(Shades(self.greenbox_image,(self.ax,self.ay)))

GUI()
