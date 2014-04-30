#!/usr/bin/python -u
import sys, string, re, math, timeit, operator

##################
## Challenge solution
##################

##################
## Summary:
##   The file 'userdata.txt' contains a list of geographic points for 4 different
##   users sorted by the time they were recorded.  The format of each line is 4
##   fields separated by a pipe character.
##
##   name|unixtime|latitude|longitude
##
##   example line:
##   danny|1335324573|37.784372722982|-122.39083248497
##
##   The program should read the file and output a list of encounters for the
##   4 users using the following rules:
##   * Generate an encounter if the users are <= 150 meters apart.
##   * If a user has not generated a point for 6 hours, consider him inactive
##     (and don't generate a new encounter).
##   * Do not generate more than one encounter per 24 hours for any pair of
##     users.
##   * Use the Haversine formula for geodesic distance calculation.
##
##   Output format for encounters:
##   unixtime|name1|latitude1|longitude1|name2|latitude2|longitude2
##   * name1 is lexigraphically lower than name2
##   * lines are sorted in ascending order by unixtime
##   * ordering for lines with the same unixtime is unspecified
##     (might as well do name1, then name2)
##
##   Example encounter output for 'danny' and 'unclejoey':
##   1327418725|danny|37.77695245908|-122.39847741481|unclejoey|37.777335807234|-122.39812024905
##
##################

##################
## Definitions and givens:
##
## Givens:
##  * userdata.txt is pre-sorted by recorded unixtime.
##  * 4 users (although don't necessarily have to limit the program to that)
##
## unixtime:  Number of seconds since 00:00:00 UTC, 01/01/1970, not counting leap seconds.
## 
## Haversine formula:
##  Function haversin(t) = sin^2(t/2) = (1 - cos(t)) / 2
##  For two points on a sphere, where:
##    * d = spherical distance between the two points
##    * r = radius of the sphere
##    * p1,p2 = latitudes of points 1 and 2
##    * l1,l2 = longitudes of points 1 and 2
##    * central angle in radians is (d/r)
##    * haversine(d/r) = haversin(p2 - p1) + ( cos(p1) * cos(p2) * haversin(l2 - l1) )
## --- Using equation from Wikipedia - Should be verified, but provides answers very close
##     to chord length with small distances.
##    * d = r arc_haversine(haversine(d/r)) = 2r arcsin(sqrt(haversine(d/r)))
##    * d = 2r arcsin(sqrt( (sin^2((p2-p1)/2) + (cos(p1) * cos(p2) * sin^2((l2-l1)/2)) ) ))
##    * NOTE:  haversine(d/r) must be in [0,1] for real d.  (Constrained by sqrt and arcsin.)
##
##################

##################
## Assumptions:
##
##  * Use  6 hrs = 3600*6  = 21600 seconds in unixtime
##  * Use 24 hrs = 3600*24 = 86400 seconds in unixtime
##  * Ignore effects of DST on intervals; local time is an adjustment from stable UTC
##    NOTE:  In reality, we might want 6 PM the following day to be considered
##           24 hours from 6 PM the previous day, whether it is 23, 24, or 25 hours.
## FIXME:  Possibly include an option to determine if a time period bridges a DST change.
##  * Ignore leap seconds.
##  * The haversine formula does not account for non-spherical earth but uses a mean radius.
##    The mean radius of the earth given by Wikipedia is about 6371 km (6371.009 km).
##
##################

##################
## Possible optimizations:
## 
##  * (1) The haversine formula is relatively expensive.  Run an approximation
##        to prune points which are obviously too far apart to bother.
##    -- Profiling results:  Using chords doesn't seem to be worth the bother for the
##                           brute force method on this data set.
##
##  * (2) Prune users' sets of other "interesting" users when other users have gone
##        inactive (doesn't really save much), are too far away to matter soon (complicated),
##        or have stopped being "interesting" for some reason (like profile changes).
##
##################

##################
## Primary algo:
##
## Goal 1:  Correctness.
##
## Goal 2:  Minimize the comparisons between base user record u0 and all following
##          records for other users.
##          * Brute force, comparing u0 and u1 individually:
##            - Move u0 when reaching another u0 record
##            - Move u0 when delta time to another user record (u1) is over 6 hours
##            - Move u0 when all his possible 24-hour encounters have been recorded
##              (not realistic in reality with a large number of users)
##            - Skip u1 if last saved encounter with u1 was within 24 hours
##            - Skip u1 if not within 150m
##          * Better way:
##            - Save the most recent time and location with a user on its update
##              (unless calculating deltas to estimate motion, the most recent is sufficient)
##            - Keep list of "friends" or other interesting users in each user
##            - On an update for a user, check last times and locations of users in
##              the list for active statuses and viable encounter distances
##
## Goal 3:  Minimize the very expensive distance calculations.  Can we estimate it
##          with a rough bounds check?  If straight line (chord) distance is >= 150m, then
##          distance along an arc would be even greater.
##          Chord length:  dX = R(cos(p2)cos(l2) - cos(p1)cos(l1))
##                         dY = R(cos(p2)sin(l2) - cos(p1)sin(l1))
##                         dZ = R(sin(p2) - sin(p1))
##                         c  = sqrt( (dX^2) + (dY^2) + (dZ^2) )
##                For any user, we would only need to calculate cos(l), cos(p), sin(l), sin(p)
##                once.  Saves an arcsin.  Sqrt is O(M(n)), trig functions are possibly
##                O((log n)^2 * M(n)).
##          NOTE:  Profiling of the entire script using the timeit module
##                 shows no benefit to enabling the chord filter for the given input file.
##                 It's almost as accurate for small distances and doesn't save much
##                 so it isn't really worth it as a gross filter.
##
## Goal 4:  The algo should ideally require one main pass through the records, if possible.
##          Use lookup tables or other structures to facilitate it.
##
##          NOTES:  On any update, a user may have moved and should re-evaluate its
##                  relationship to all other users of interest.
##                  So really we have O(u*n), where for each update (n of them), we evaluate
##                  an average of u users, where u is the average number of other users of
##                  interest for each user.
##          IDEAS:  - For each user, a list of other interesting users and a lookup
##                    table (or set) to hold a subset.  Prune the subset based on large
##                    distances or inactive users, to reduce the size of u in O(u*n).
##                    Requires broadcast-type updates from users of mutual interest to
##                    re-add a user into the subset.  Many small location updates by the
##                    user could also bring it into an encounter with a pruned user before
##                    it is re-added.
##                  - ...
##
##################


#####################
#### CODE BEGINS ####
#####################

# Global options to set through command line arguments.  They can be hardwired here,
# but it's not necessary.
# The approximate dist filter uses chord length to decide if it should use the Haversine
# formula for a better answer.
do_debug = False
use_approx_dist_filter = False
use_brute_force_method = False
skip_printing_for_profiling = False
sort_encounter_list = False
# reading_file = False

## 360 degrees = 2*pi radians
## Can use library functions math.radians(x) and math.degrees(x)
# k_DegToRadMult = math.pi / 180.0 

# 6 hour and 24 hour time limit constants
kHl_UserActiveTimeLimit = 21600
kHl_EncounterTimeLimit  = 86400
# 150 meter max distance for an encounter
kHl_MaximumEncounterDistance = 150.0
kHl_MaximumApproxDistanceWithBuffer = kHl_MaximumEncounterDistance + 100.0
# 6371.009 km or 6,371,009 m average radius for the Earth
kHl_EarthRadiusMeters = 6371009.0

# Constants for quadrant 2 and 4 boundaries to multiply cos/sin conversion by (-1)
# These should only be used for the chord length approximation
kHl_Quad2MinRadians = math.pi / 2.0
kHl_Quad2MaxRadians = math.pi
kHl_Quad4MinRadians = -1.0 * kHl_Quad2MinRadians
kHl_Quad4MaxRadians = 0.0


#####################
##### Class definitions
#####################

### HlLocation class ###
#   It holds latitude and longitude values in up to three formats.  To save some space,
#   it initially has zero references or values.
#   -- NOTE:  The class bothers with all three to avoid assuming the input file and output
#             file formats the latitude and longitude strings as ".14g" (14 digit precision, general).
#             Saving the input string makes it easy to match all digits in later output.
#   When instantiating the class, provide the latitude and longitude as signed decimal strings,
#   where both latitude and longitude are in degrees between -180 and 180.
#
#   Usage:  myNewLocation = HlLocation(latitude_degrees_string, longitude_degrees_string)
class HlLocation:
    latD   = None  # floats for lat, long in degrees
    longD  = None
    latDS  = None  # strings for lat, long (given input)
    longDS = None
    latR   = None  # floats for lat, long in radians
    longR  = None

    # Initialize a new location object, given latitude and longitude as signed decimal strings
    def __init__(self, inLat, inLong):
        self.latDS = inLat
        self.longDS = inLong

    # String - Get the initial latitude string (degrees)
    def latitudeString(self):            
        return self.latDS

    # String - Get the initial longitude string (degrees)
    def longitudeString(self):
        return self.longDS


    # float - Return the longitude in either radians (-pi to pi) or degrees (assumes -180 to 180)
    #         If results are not already stored, perform any necessary conversions and store them.
    # Usage:  longInRadians = locObject.longitude(True)
    #         longInDegrees = locObject.longitude(False)
    def longitude(self, useRadians):
        if(useRadians):
            if(self.longR == None):
                self.longR = math.radians(float(self.longDS))
            return self.longR
        else:
            if(self.longD == None):
                self.longD = float(self.longDS)
            return self.longD

    # float - Return the latitude in either radians (-pi to pi) or degrees (assumes -180 to 180)
    #         If results are not already stored, perform any necessary conversions and store them.
    # Usage:  latInRadians = locObject.latitude(True)
    #         latInDegrees = locObject.latitude(False)
    def latitude(self, useRadians):
        if(useRadians):
            if(self.latR == None):
                self.latR = math.radians(float(self.latDS))
            return self.latR
        else:
            if(self.latD == None):
                self.latD = float(self.latDS)
            return self.latD


### HlEncounter class ###
#   It holds the two user names, two locations, and posted unixtime for an
#   encounter between two users.  The posted unixtime corresponds to the timestamp
#   for the later of the two entries triggering the valid encounter.
#   The valid flag should be True except for an attempt to create an encounter for
#   a user with itself.  It does not check for invalid inputs otherwise.
#   An encounter can print itself in the desired format.
#
#   Usage:  newEncounter = HlEncounter(user0_name, user0_lastUpdateTime, user0_lastUpdateLocation,
#                                      user1_name, user1_encounterTime,  user1_encounterLocation)
#           newEncounter.printSelf()
class HlEncounter:
    username1 = None    # user names
    username2 = None
    loc1  = None        # user locations
    loc2  = None
    time  = None        # later timestamp (usually when user1's report caused an encounter)
    valid = False       # encounter is valid

    # Initialize a new HlEncounter object with time stamp, user names, and user locations
    def __init__(self, inTime, inUsername1, inLoc1, inUsername2, inLoc2):
        if(inUsername1 == inUsername2):   # invalid encounter with one's self
            if(do_debug):
                print 'ERROR:  Attempted to create an invalid encounter with user1 %s and user2 %s\n' % (inUser1, inUser2)
            self.valid = False
            return
        elif(inUsername1 < inUsername2):  # order lexigraphically for output; expected order
            self.username1 = inUsername1
            self.username2 = inUsername2
            self.loc1  = inLoc1
            self.loc2  = inLoc2
        else:                             # swap when input order is reversed
            self.username1 = inUsername2
            self.username2 = inUsername1
            self.loc1  = inLoc2
            self.loc2  = inLoc1
        self.time  = inTime
        self.valid = True

    # Void - Print all the important values in a specific single-line format
    # Usage:  newEncounter.printSelf()
    #   <unixtime_integer>|<first_alphabetical_username>|<signed_decimal_string>|<signed_decimal_string>|<second_alphabetical_username>|<signed_decimal_string>|<signed_decimal_string>
    #   Example:  1327418725|danny|37.77695245908|-122.39847741481|unclejoey|37.777335807234|-122.39812024905
    def printSelf(self):
        if(self.valid):
            print '%d|%s|%s|%s|%s|%s|%s' % (
                self.time, self.username1,
                self.loc1.latitudeString(), self.loc1.longitudeString(),
                self.username2,
                self.loc2.latitudeString(), self.loc2.longitudeString())
        elif(do_debug):
            print 'ERROR:  Invalid encounter, most likely the users were equal.';


### HlDataEntry class ###
#   It holds the username, unixtime, and location of a data update in the input file.
#   When instantiating it, provide a string with a line from the input file, or a
#   string matching its format.  The format is the following four fields separated by
#   pipe characters, with no leading whitespace:
#     <username>|<long_integer_unixtime>|<signed_floating_point_latitude_degrees>|<signed_floating_point_longitude_degrees>
#   Example:
#     danny|1327401809|37.775011290418|-122.39381636393
#
# Usage:  newDataEntry = HlDataEntry(inputLine)
class HlDataEntry:
    username  = None
    time      = None
    loc       = None
    valid     = False

    # Initialize a new data entry from an input string
    def __init__(self, inString):
        inString = inString.rstrip('\r\n')      # strip end-of-line characters
        columns = string.split(inString, '|')   # split string into fields
        numColumns = len(columns)
        if(numColumns > 0):                     
            if(numColumns != 4):                # there should be four fields for a valid entry
                if(do_debug):
                    print 'ERROR:  Invalid data entry line - does not have 4 elements separated by pipe characters.\n';
                    return
            self.username = columns[0]          # username is first
            self.time     = long(columns[1])    # convert time from string to long integer
            self.loc      = HlLocation(columns[2], columns[3])  # create location object with strings
            self.valid = True


    # Void - Set the username to a new string
    # Not currently used.
    def setUsername(self, inUsername):
        self.username = inUsername
    

    # Void - Set the time stamp to a new long integer value
    # Not currently used.
    def setTime(self, inTime):
        self.time = inTime


    # Void - Set the location object reference to a new location object
    # Not currently used.
    def setLoc(self, inLoc):
        self.loc = inLoc


    # Boolean - Check if the data entry is currently valid
    def isValid(self):
        return self.valid


### HlUser class ###
#   It holds the name, last unixtime posted during the current processing cycle,
#   the last location posted during the current processing cycle, and a dictionary
#   pairing other users with the time stamps of their last shared encounters.
#   For the purpose of just creating a user with a given name, the time and location
#   can be initially set to None and updated later.
# Usage:  newUser = HlUser(username, post_time, post_loc_object)
class HlUser:
    name = None                   # user name
    lastPostedTime = None         # last unixtime posted during processing cycle
    lastPostedLoc  = None         # last location posted during processing cycle
    userEncounterDict = None      # lookup table for encounter times with other users
    otherUserSet = None           # set of other interesting users to check for encounters
    lastPostedLocCosP = None      # calculated cos(p) for the last posted location - updated when needed

    # Initialize a user with a name string, posted time value, and posted location object
    # Create an empty encounter lookup table and empty set of other interesting users
    def __init__(self, inName, time, loc):
        self.name = inName
        self.lastPostedTime = time
        self.lastPostedLoc = loc
        self.lastPostedLocCosP = None
        self.userEncounterDict = {}
        self.otherUserSet = set()


    # Void - Update the last posted time
    def updateLastPostedTime(self, time):
        self.lastPostedTime = time
    

    # Void - Update the last posted location object reference
    #        Clear the obsolete cos(p) value; recalc only when requested
    def updateLastPostedLoc(self, loc):
        self.lastPostedLoc = loc
        self.lastPostedLocCosP = None


    # Void - Create or update the stored unixtime for an encounter with a user
    def updateEncounterWithUser(self, user, time):
        if(user != None):
            self.userEncounterDict[user.name] = time
        else:
            print 'ERROR: User provided for encounter update with %s is None.' % (self.name)


    # Long - Return the last unixtime for an encounter with a user,
    #        or --None-- if one has not yet occurred.
    def lastEncounterWithUser(self, user):
        if(user != None):
            if(user.name in self.userEncounterDict):
                return self.userEncounterDict[user.name]
        return None


    # Void - Add new user to set if it doesn't exist
    def addInterestingUser(self, user):
        if(user not in self.otherUserSet):
            self.otherUserSet.add(user)


    # Boolean - Check if other user is of interest to this one
    def isUserInteresting(self, user):
        return (user in self.otherUserSet)


    # Set - Return the set of all other interesting users
    def allOtherInterestingUsers(self):
        return self.otherUserSet


    # Void - Clean up list of interesting users; currently just removes self
    #        if it was added by accident.
    def cleanInterestingUsers(self):
        if(self in self.otherUserSet):
            self.otherUserSet.discard(self)


    # Boolean - Return true if the time argument is valid and greater than or equal
    #           to the user's saved time, and the delta between the two is less than
    #           the active time limit.
    def userIsStillActive(self, time):
        if(time != None):
            if(self.lastPostedTime == None):
                return False
            deltaT = time - self.lastPostedTime
            if(deltaT < 0):                         # deltaT shouldn't be neg if doing in order
                return False
            if(deltaT < kHl_UserActiveTimeLimit):   
                return True
        return False


    # Boolean - Return true if the user has been encountered previously, the
    #           time argument is greater than or equal to the last encounter time,
    #           and the delta between the two is less than the encounter time limit.
    def alreadyEncounteredUserWithinLimit(self, user, time):
        if((user != None) and (time != None)):                     # want valid arguments
            lastEncounterTime = self.lastEncounterWithUser(user)   # lookup last encounter time
            if(lastEncounterTime != None):                         # we have one, so calc delta
                deltaT = time - lastEncounterTime
                if(deltaT < 0):                    # deltaT shouldn't be neg if doing in order
                    return False
                if(deltaT < kHl_EncounterTimeLimit):
                    return True
        return False


    # float - Return the cos(p) value for the last posted location.
    #         If the cached value doesn't exist, calculated it and cache it for
    #         other possible comparisons with this user.
    def cosPValForLastPostedLocation(self):
        if(self.lastPostedLocCosP == None):
            self.lastPostedLocCosP = math.cos(self.lastPostedLoc.latitude(True))
        return self.lastPostedLocCosP


    # Boolean - Return true if distance from this user to another is less than
    #           the global encounter distance limit.  Optionally filter
    #           first with chord distance before running Haversine function.
    #           Chords are smaller than surface arcs, so if a chord distance is
    #           greater than the limit, the Haversine distance should also be greater.
    #
    #           Chords are an excellent approximation for positions that are already
    #           very close, but they may not save much computation.  Skip the
    #           approximation option unless using a faster filter.
    def distanceToUserWithinLimit(self, user, approxFirst):
        if(user != None):
            if((self.lastPostedLoc != None) and
               (user.lastPostedLoc != None)):
                if(approxFirst):         # do chord approximation first if desired, with small buffer
                    if(self.distanceToUserSimpleChord(user) > kHl_MaximumApproxDistanceWithBuffer):
                        return False
                # do the Haversine formula if we fall through
                if(self.distanceToUserHaversine(user) <= kHl_MaximumEncounterDistance):
                    return True
        return False
    

    # float - Return the distance between this user and another user using
    #         the Haversine formula.
    def distanceToUserHaversine(self, user):
        p1 = self.lastPostedLoc.latitude(True)
        p2 = user.lastPostedLoc.latitude(True)
        l1 = self.lastPostedLoc.longitude(True)
        l2 = user.lastPostedLoc.longitude(True)

        # Once these are calculated they can be re-used until next location update,
        # so they are provided by and cached in the user objects.
        cosp1 = self.cosPValForLastPostedLocation()
        cosp2 = user.cosPValForLastPostedLocation()

        sinDeltaHalfP = math.sin((p2 - p1)/2.0)
        sinDeltaHalfL = math.sin((l2 - l1)/2.0)
        sin2DeltaHalfP = sinDeltaHalfP * sinDeltaHalfP
        sin2DeltaHalfL = sinDeltaHalfL * sinDeltaHalfL

        dist = 2 * kHl_EarthRadiusMeters * (
            math.asin(math.sqrt(sin2DeltaHalfP + (cosp1 * cosp2 * sin2DeltaHalfL))))
        return dist

    
    # float - Return the distance between this user and another user using
    #         the sphere chord length formula (from dX, dY, dZ).
    #         This is only an optional optimization to remove an arcsin()
    #         function, although it adds some sqrt() calls.  The values
    #         are quite close to the Haversine formula for small distances.
    def distanceToUserSimpleChord(self, user):
        p1 = self.lastPostedLoc.latitude(True)
        p2 = user.lastPostedLoc.latitude(True)
        l1 = self.lastPostedLoc.longitude(True)
        l2 = user.lastPostedLoc.longitude(True)

        # Once these are calculated they can be re-used until next location update,
        # so they are provided by and cached in the user objects.  They are common
        # to this optional function and the required Haversine formula.
        cosp1 = self.cosPValForLastPostedLocation()
        cosp2 = user.cosPValForLastPostedLocation()

        # These are not needed in the Haversine formula so they aren't cached.
        # They could be...
        cosl1 = math.cos(l1)
        cosl2 = math.cos(l2)

        sinp1 = self.sinFromCos(p1, cosp1)
        sinp2 = self.sinFromCos(p2, cosp2)
        sinl1 = self.sinFromCos(l1, cosl1)
        sinl2 = self.sinFromCos(l2, cosl2)

        deltaX = kHl_EarthRadiusMeters * ((cosp2 * cosl2) - (cosp1 * cosl1))
        deltaY = kHl_EarthRadiusMeters * ((cosp2 * sinl2) - (cosp1 * sinl1))
        deltaZ = kHl_EarthRadiusMeters * (sinp2 - sinp1)
        dist = math.sqrt((deltaX * deltaX) + (deltaY * deltaY) + (deltaZ * deltaZ))
        return dist
    
    # float - Return sin(x) given cos(x) and x.  Uses sqrt instead of sin(x)
    #         and adjusts sign of sin(x) for quadrant of x.
    def sinFromCos(self, angle, cosVal):
        # quadrant 1, cos+/sin+  1.0 mult
        # quadrant 2, cos-/sin+ -1.0 mult
        # quadrant 3, cos-/sin-  1.0 mult
        # quadrant 4, cos+/sin- -1.0 mult
        # sin^2(x) + cos^2(x) = 1
        # sin(x) = (sign) * sqrt(1 - cos^2(x))
        sinVal = math.sqrt(1 - (cosVal * cosVal))
        if(((angle >= kHl_Quad2MinRadians) and (angle < kHl_Quad2MaxRadians)) or
           ((angle >= kHl_Quad4MinRadians) and (angle < kHl_Quad4MaxRadians))):
            sinVal = -1.0 * sinVal
        return sinVal
    

### HlProcessor class ###
#   This class handles the processing of the user data file.  It holds a
#   list of data entries from the file, a lookup table pairing user names
#   with user objects, and a list of valid encounters between users.
#   NOTE:  The list of valid encounters is empty until findEncounters() is called!
#
#   Inputs:  string   - input file name
#            booleans - use chord length approximation filter, extra final sort
#
#   Usage:  newProcessor = HlProcessor(input_file_name, useApproxFilter, extraEncounterSort)
#           newProcessor.findEncounters()
#           newProcessor.printEncounters()
class HlProcessor:
    encounterList = None          # list of user encounter (HlEncounter) objects
    userDict = None               # dict of user (HlUser) objects with names as keys
    file = None                   # input file
    fileLines = None              # lines from the file
    filterWithApprox = False      # optional filter flag for using chord approximations
    sortFinalList = False         # optional filter flag to sort encounter output (consistency for same unixtime)
    dataEntries = None            # list of data entry (HlDataEntry) objects
    totalLineCount = 0            # file line count
    currentLineIdx = 0            # current line index
    
    # Initialize the processor with a file name and flags for the
    # optional filter and optional sort of encounters (for consistent
    #  ordering of multiple encounters with the same unixtime).
    def __init__(self, filename, useApproxFilter, extraEncounterSort):
        if(filename == None):
            print 'ERROR:  A valid input file name was not provided to the processor object.\n'
            exit(1)
        self.file = filename
        self.filterWithApprox = useApproxFilter
        self.sortFinalList = extraEncounterSort

        try:       # attempt to open file for reading or exit with failure message
            fileInput = open(self.file, 'r')
        except:
            print 'ERROR:  Could not open file %s for reading.\n' % (self.file)
            exit(1)
        
        self.fileLines = fileInput.readlines()    # read and close file as soon as possible
        fileInput.close()
        self.totalLineCount = len(self.fileLines) # get line count and create empty structures
        self.dataEntries = []
        self.encounterList = []
        self.userDict = {}
   
    # HlDataEntry - Return an HlDataEntry object for the entry with a given index
    # If an entry is requested that has not already been processed, process as many
    # entries as needed to retrieve it.  Only count lines with valid data as an entry.
    # NOTE:  This function exists mostly as an abstraction, since we could prepare the
    #        entire list at once from the file data.  In reality, the entries may be
    #        broadcast over the Internet and waiting in a queue to be processed.
    def getDataEntry(self, entryIdx):
        numParsedEntries = len(self.dataEntries)
        if(entryIdx < numParsedEntries):
            return self.dataEntries[entryIdx]
        else:
            entriesToAdd = 1 + entryIdx - numParsedEntries  # e.g. entry 0, 0 parsed, need to read 1
            while((entriesToAdd > 0) and (self.currentLineIdx < self.totalLineCount)):
                newDataEntry = HlDataEntry(self.fileLines[self.currentLineIdx])
                if(newDataEntry.isValid()):
                    self.incorporateDataEntryAndUserIfNew(newDataEntry)
                    entriesToAdd -= 1
                self.currentLineIdx += 1
            if(entryIdx < len(self.dataEntries)):
                return self.dataEntries[entryIdx]
            return None
             
    # Void - Add a new data entry; if the user mapping doesn't exist, create the user object,
    #        update everyone's sets of interesting users, and add the mapping of the user
    #        object in the user dict.
    def incorporateDataEntryAndUserIfNew(self, dataEntry):
        # we should only call this if dataEntry is already deemed to be valid
        self.dataEntries.append(dataEntry)
        if(not dataEntry.username in self.userDict):
            newUser = HlUser(dataEntry.username, None, None)
            if(newUser != None):
                self.updateInterestingUserSets(newUser)
                self.userDict[newUser.name] = newUser

    # Void - For each user already in the user dict create mutual
    #        entries for that user and the new user in their sets
    #        of interesting users.
    #        Just in case the new user was already added to the user dict,
    #        remove a self-reference for the new user if it exists.
    def updateInterestingUserSets(self, newUser):
        # In this special problem, everyone is interesting to everyone else.
        for user in self.userDict.values():
            user.addInterestingUser(newUser)
            newUser.addInterestingUser(user)
        # Remove self-interest if we added it unintentionally (i.e., already in user dict)
        newUser.cleanInterestingUsers()

    # Void - Add a new encounter object with the data for a valid encounter
    #        to the processor's list of encounters.  The users should hold
    #        their latest info at the time of the encounter, which is the later
    #        of the two time stamps.
    #        Update the user encounter lookup tables within both users for
    #        later checks for the same people within the encounter time limit.
    def addEncounter(self, user0, user1):
        latestTime = max(user0.lastPostedTime, user1.lastPostedTime)   # time of latest entry
        user0.updateEncounterWithUser(user1, latestTime)               # update each other's lookup table
        user1.updateEncounterWithUser(user0, latestTime)
        self.encounterList.append(HlEncounter(latestTime, user0.name, user0.lastPostedLoc,
                                              user1.name, user1.lastPostedLoc))

    # Void - Update any interesting user state from the current data entry.
    #        (serves mostly as abstraction)
    def updateUserStateFromEntry(self, user, entry):
        user.updateLastPostedTime(entry.time)
        user.updateLastPostedLoc(entry.loc)


###############
######### Key encounter processing function
###############
    # Void - Find all valid encounters from the entire data set, starting with entry 0
    #        NOTE:  The use of getDataEntry() is abstracted such that it could be the interface
    #               to a queue of broadcasted updates with little change to this function.
    def findEncounters(self):
        entryIdx = 0
        entry = self.getDataEntry(entryIdx)       # get initial entry; function populates userDict
        while(entry != None):                     # loop while we have remaining entries
            user = self.userDict[entry.username]  # get user for current entry and update its state
            self.updateUserStateFromEntry(user, entry)
            
            for otherUser in user.allOtherInterestingUsers():     # for all of this user's interesting users
                if(not otherUser.userIsStillActive(entry.time)):  # skip user if inactive
                    continue
                if(not user.alreadyEncounteredUserWithinLimit(otherUser, entry.time)):
                    if(user.distanceToUserWithinLimit(otherUser, self.filterWithApprox)):
                        self.addEncounter(user, otherUser)        # add encounter if new and close enough

            entryIdx += 1                       # update entry index and fetch next
            entry = self.getDataEntry(entryIdx) # -- entry will be None when no more exist
        if(self.sortFinalList):                    # optionally sort the final list of encounters for
            self.sortEncountersCompletely()        #  consistency with multiple identical time stamps


    # OPTIONAL AND *OBSOLETE*
    # Void - This is an early version of the function that implements a
    #        brute force approach to finding valid encounters, assuming
    #        everyone is interesting to everyone else and requiring less
    #        saved state and fewer lookup mechanisms (like sets of interesting users).
    #        It looks at entries multiple times, making it very inefficient.
    #        (It also changed as more structures were added to develop the
    #         better version above.)
    def findEncountersBruteForce(self):
        user0EntryIdx = 0
        user0Entry = self.getDataEntry(user0EntryIdx)
        while(user0Entry != None):
            user0 = self.userDict[user0Entry.username]
            self.updateUserStateFromEntry(user0, user0Entry)

            user1EntryIdx = user0EntryIdx + 1
            user1Entry = self.getDataEntry(user1EntryIdx)
            while(user1Entry != None):
                if(user1Entry.username == user0Entry.username):
                    break
                user1 = self.userDict[user1Entry.username]
                self.updateUserStateFromEntry(user1, user1Entry)

                if(not user0.userIsStillActive(user1Entry.time)):
                    break
                if(not user0.alreadyEncounteredUserWithinLimit(user1, user1Entry.time)):
                    if(user0.distanceToUserWithinLimit(user1, self.filterWithApprox)):
                        self.addEncounter(user0, user1)
                user1EntryIdx += 1
                user1Entry = self.getDataEntry(user1EntryIdx)
            user0EntryIdx += 1
            user0Entry = self.getDataEntry(user0EntryIdx)
        # sort encounters by time stamp - using this method, some might be out of order
        # self.sortEncounterTimes()
        self.sortEncountersCompletely()


    # Void - Sort the object's encounter list based only on unixtime stamps
    def sortEncounterTimes(self):
        sortedEncounters = sorted(self.encounterList, key=lambda enc: enc.time)
        self.encounterList = sortedEncounters

    # Void - Sort the object's encounter list by unixtime, then by username1, then by username2
    #        This will make output consistent for encounters of different user pairs with the
    #        same unixtime values.
    def sortEncountersCompletely(self):
        sortedEncounters = sorted(self.encounterList, key=operator.attrgetter('time', 'username1', 'username2'))
        self.encounterList = sortedEncounters

    # Void - Ask all encounters to print themselves to stdout.
    def printEncounters(self):
        for encounter in self.encounterList:
            encounter.printSelf()



################
##### Global Functions
################

# Void - Print the expected script usage, including optional arguments for help and debug.
#        Pass the function a True value to exit the script afer printing the usage.
def printUsage(doExit):
    if(len(sys.argv) > 0):
        scriptName = sys.argv[0]
    else:
        scriptName = 'Script'
    print scriptName + ' usage:  ' + scriptName + ' [-[a|b|d|h|p|s]] [input_file]'
    print '  If called without an input_file argument, the script will look for a file named userdata.txt.'
    print '  Other optional arguments can be combined, can appear before or after the input file, and include:'
    print '    -a:  enable filtering of distance calculations based on chord approximations'
    print '    -b:  use the brute force method of processing the data entries; adds final sort'
    print '    -d:  enable printing of extra debugging information'
    print '    -h:  print this help information and exit'
    print '    -p:  skip printing encounters (used for profiling)'
    print '    -s:  optionally sort final encounter list for consistent ordering of names with same unixtime'
    print '         (brute force method automatically includes the final sort)'
    print
    if(doExit):
        exit(1)


# String - This function parses the supplied arguments and returns the file name in a string.
#          If no bare file name has been provided, it assumes the file is userdata.txt.
#          If an optional argument is incorrect or requests help, then the function will
#          print the script usage and exit.  If more one string is supplied without a
#          leading dash, the function will also print the script usage and exit.
#          It is flexible enough to support combined optional arguments (like '-ds').
def parseArguments():
    global do_debug, use_approx_dist_filter, use_brute_force_method, skip_printing_for_profiling
    global sort_encounter_list
    fileArgument = None
    argLength = len(sys.argv)
    if(argLength > 1):
        for currentArgument in range(1, argLength):
            argString = sys.argv[currentArgument]
            argStringLength = len(argString)
            if(argStringLength > 0):
                if(argString[0] == '-'):
                    if(argStringLength == 1):
                        printUsage(True)
                    currentCharIndex = 1
                    while(currentCharIndex < argStringLength):
                        if(argString[currentCharIndex] == 'h'):
                            printUsage(True)
                    
                        if(argString[currentCharIndex] == 'd'):
                            do_debug = True
                        elif(argString[currentCharIndex] == 'a'):
                            use_approx_dist_filter = True
                        elif(argString[currentCharIndex] == 'b'):
                            use_brute_force_method = True
                        elif(argString[currentCharIndex] == 'p'):
                            skip_printing_for_profiling = True
                        elif(argString[currentCharIndex] == 's'):
                            sort_encounter_list = True
                        else:
                            print '"' + argString[currentCharIndex] + '" is not a valid option.'
                            printUsage(True)
                        currentCharIndex += 1
                else:
                    if(fileArgument != None):   # quit if we've already seen a bare file name
                        print 'Please pass the script a maximum of one input file name.'
                        printUsage(True)
                    fileArgument = argString    # otherwise, use it as the input file
    if(fileArgument == None):           # use the problem's initial input file as default
        fileArgument = "userdata.txt"
    return fileArgument


################
##### MAIN
################

#fileArgument = "userdata.txt"
fileArgument = parseArguments()   # set options and get input file name

# If debugging, print out the options
if(do_debug):
    print "Running with do_debug %d, use_approx_dist_filter %d, use_brute_force_method %d, skip_printing_for_profiling %d, sort_encounter_list %d" % (do_debug, use_approx_dist_filter, use_brute_force_method,
                                                                                                                                                      skip_printing_for_profiling, sort_encounter_list)

# Create a processor and read the input file
processor = HlProcessor(fileArgument, use_approx_dist_filter, sort_encounter_list)

if(use_brute_force_method):                  # call the obsolete method if desired
    processor.findEncountersBruteForce()
else:                                        # call the better one by default
    processor.findEncounters()

if(not skip_printing_for_profiling):         # print encounters unless profiling
    processor.printEncounters()


