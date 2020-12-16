:- discontiguous point/2, distance/3.
:- multifile point/2, distance/3.
/*
	Travelling Salaesman Data from:
	"Solution of a Large-Scale Traveling-Salesman Problem"
	http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.606.2752&rep=rep1&type=pdf
*/
point( 1, 'Manchester').
point( 2, 'Montpelier').
point( 3, 'Detroit').
point( 4, 'Cleveland').
point( 5, 'Charleston'). 
point( 6, 'Louisville').
point( 7, 'Indianapolis').
point( 8, 'Chicago').
point( 9, 'Milwaukee').
point(10, 'Minneapolis').
point(11, 'Pierre').
point(12, 'Bismarck').
point(13, 'Helena').
point(14, 'Seattle').
point(15, 'Portland').
point(16, 'Boise').
point(17, 'SaltLakeCity'). 
point(18, 'CarsonCity'). 
point(19, 'LosAngeles').
point(20, 'Phoenix').
point(21, 'SantaFe').
point(22, 'Denver'). 
point(23, 'Cheyenne').
point(24, 'Omaha').
point(25, 'DesMoines').
point(26, 'KansasCity').
point(27, 'Topeka').
point(28, 'OklahomaCity').
point(29, 'Dallas').
point(30, 'LittleRock').
point(31, 'Memphis').
point(32, 'Jackson').
point(33, 'NewOrleans'). 
point(34, 'Birmingham').
point(35, 'Atlanta').
point(36, 'Jacksonville').
point(37, 'Columbia').
point(38, 'Raleigh').
point(39, 'Richmond').
point(40, 'Washington').
point(41, 'Boston').
point(42, 'Portland').

%
% distance(CityNum1, CityNum2, Dunits)
%    where D units is the distance in miles, less 11, divided by 17 and rounded to nearest integer

distance(C1,C2,D) :-
	C1>C2,!,
	distance(C2,C1,D).
	
distance( 1,  2,   8).
distance( 1,  3,  39).
distance( 1,  4,  37).
distance( 1,  5,  50).
distance( 1,  6,  61).
distance( 1,  7,  58).
distance( 1,  8,  59).
distance( 1,  9,  62).

distance( 1, 10,  81).
distance( 1, 11, 103).
distance( 1, 12, 108).
distance( 1, 13, 145).
distance( 1, 14, 181).
distance( 1, 15, 187).
distance( 1, 16, 161).
distance( 1, 17, 142).
distance( 1, 18, 174).
distance( 1, 19, 185).

distance( 1, 20, 164).
distance( 1, 21, 137).
distance( 1, 22, 117).
distance( 1, 23, 114).
distance( 1, 24,  85).
distance( 1, 25,  77).
distance( 1, 26,  87).
distance( 1, 27,  91).
distance( 1, 28, 105).
distance( 1, 29, 111).

distance( 1, 30,  91).
distance( 1, 31,  83).
distance( 1, 32,  89).
distance( 1, 33,  95).
distance( 1, 34,  74).
distance( 1, 35,  67).
distance( 1, 36,  74).
distance( 1, 37,  57).
distance( 1, 38,  45).
distance( 1, 39,  35).
	
distance( 1, 40,  29).
distance( 1, 41,   3).
distance( 1, 42,   5).

distance( 2,  3,  45).
distance( 2,  4,  47).
distance( 2,  5,  49).
distance( 2,  6,  62).
distance( 2,  7,  60).
distance( 2,  8,  60).
distance( 2,  9,  66).

distance( 2, 10,  81).
distance( 2, 11, 107).
distance( 2, 12, 117).
distance( 2, 13, 149).
distance( 2, 14, 185).
distance( 2, 15, 191).
distance( 2, 16, 170).
distance( 2, 17, 146).
distance( 2, 18, 178).
distance( 2, 19, 186).

distance( 2, 20, 165).
distance( 2, 21, 139).
distance( 2, 22, 122).
distance( 2, 23, 118).
distance( 2, 24,  89).
distance( 2, 25,  80).
distance( 2, 26,  89).
distance( 2, 27,  93).
distance( 2, 28, 106).
distance( 2, 29, 113).

distance( 2, 30,  92).
distance( 2, 31,  85).
distance( 2, 32,  91).
distance( 2, 33,  97).
distance( 2, 34,  81).
distance( 2, 35,  69).
distance( 2, 36,  76).
distance( 2, 37,  59).
distance( 2, 38,  46).
distance( 2, 39,  37).

distance( 2, 40,  33).
distance( 2, 41,  11).
distance( 2, 42,  12).

distance( 3,  4,   9).
distance( 3,  5,  21).
distance( 3,  6,  21).
distance( 3,  7,  16).
distance( 3,  8,  15).
distance( 3,  9,  20).

distance( 3, 10,  40).
distance( 3, 11,  62).
distance( 3, 12,  66).
distance( 3, 13, 104).
distance( 3, 14, 140).
distance( 3, 15, 146).
distance( 3, 16, 120).
distance( 3, 17, 101).
distance( 3, 18, 133).
distance( 3, 19, 142).

distance( 3, 20, 120).
distance( 3, 21,  94).
distance( 3, 22,  77).
distance( 3, 23,  73).
distance( 3, 24,  44).
distance( 3, 25,  36).
distance( 3, 26,  44).
distance( 3, 27,  48).
distance( 3, 28,  62).
distance( 3, 29,  69).

distance( 3, 30,  50).
distance( 3, 31,  42).
distance( 3, 32,  55).
distance( 3, 33,  64).
distance( 3, 34,  44).
distance( 3, 35,  42).
distance( 3, 36,  61).
distance( 3, 37,  46).
distance( 3, 38,  41).
distance( 3, 39,  35).
distance( 3, 40,  30).
distance( 3, 41,  41).
distance( 3, 42,  55).

distance( 4,  5,  15).
distance( 4,  6,  20).
distance( 4,  7,  17).
distance( 4,  8,  20).
distance( 4,  9,  25).

distance( 4, 10,  44).
distance( 4, 11,  67).
distance( 4, 12,  71).
distance( 4, 13, 108).
distance( 4, 14, 144).
distance( 4, 15, 150).
distance( 4, 16, 124).
distance( 4, 17, 104).
distance( 4, 18, 138).
distance( 4, 19, 143).

distance( 4, 20, 123).
distance( 4, 21,  96).
distance( 4, 22,  80).
distance( 4, 23,  78).
distance( 4, 24,  48).
distance( 4, 25,  40).
distance( 4, 26,  46).
distance( 4, 27,  50).
distance( 4, 28,  63).
distance( 4, 29,  71).

distance( 4, 30,  51).
distance( 4, 31,  43).
distance( 4, 32,  55).
distance( 4, 33,  63).
distance( 4, 34,  43).
distance( 4, 35,  41).
distance( 4, 36,  60).
distance( 4, 37,  41).
distance( 4, 38,  34).
distance( 4, 39,  26).

distance( 4, 40,  21).
distance( 4, 41,  37).
distance( 4, 42,  41).

distance( 5,  6,  17).
distance( 5,  7,  18).
distance( 5,  8,  26).
distance( 5,  9,  31).

distance( 5, 10,  50).
distance( 5, 11,  72).
distance( 5, 12,  77).
distance( 5, 13, 114).
distance( 5, 14, 150).
distance( 5, 15, 156).
distance( 5, 16, 130).
distance( 5, 17, 111).
distance( 5, 18, 143).
distance( 5, 19, 140).

distance( 5, 20, 124).
distance( 5, 21,  94).
distance( 5, 22,  83).
distance( 5, 23,  84).
distance( 5, 24,  53).
distance( 5, 25,  46).
distance( 5, 26,  46).
distance( 5, 27,  48).
distance( 5, 28,  64).
distance( 5, 29,  66).

distance( 5, 30,  46).
distance( 5, 31,  38).
distance( 5, 32,  50).
distance( 5, 33,  56).
distance( 5, 34,  35).
distance( 5, 35,  31).
distance( 5, 36,  42).
distance( 5, 37,  25).
distance( 5, 38,  20).
distance( 5, 39,  18).

distance( 5, 40,  18).
distance( 5, 41,  47).
distance( 5, 42,  53).

distance( 6,  7,   6).
distance( 6,  8,  17).
distance( 6,  9,  22).

distance( 6, 10,  41).
distance( 6, 11,  63).
distance( 6, 12,  68).
distance( 6, 13, 106).
distance( 6, 14, 142).
distance( 6, 15, 142).
distance( 6, 16, 115).
distance( 6, 17,  97).
distance( 6, 18, 129).
distance( 6, 19, 130).

distance( 6, 20, 106).
distance( 6, 21,  80).
distance( 6, 22,  68).
distance( 6, 23,  69).
distance( 6, 24,  41).
distance( 6, 25,  34).
distance( 6, 26,  30).
distance( 6, 27,  34).
distance( 6, 28,  47).
distance( 6, 29,  51).

distance( 6, 30,  30).
distance( 6, 31,  22).
distance( 6, 32,  34).
distance( 6, 33,  42).
distance( 6, 34,  23).
distance( 6, 35,  25).
distance( 6, 36,  44).
distance( 6, 37,  30).
distance( 6, 38,  34).
distance( 6, 39,  34).

distance( 6, 40,  35).
distance( 6, 41,  57).
distance( 6, 42,  64).

distance( 7,  8,  10).
distance( 7,  9,  15).

distance( 7, 10,  35).
distance( 7, 11,  57).
distance( 7, 12,  61).
distance( 7, 13,  99).
distance( 7, 14, 135).
distance( 7, 15, 137).
distance( 7, 16, 110).
distance( 7, 17,  91).
distance( 7, 18, 123).
distance( 7, 19, 126).

distance( 7, 20, 106).
distance( 7, 21,  78).
distance( 7, 22,  62).
distance( 7, 23,  63).
distance( 7, 24,  34).
distance( 7, 25,  27).
distance( 7, 26,  28).
distance( 7, 27,  32).
distance( 7, 28,  46).
distance( 7, 29,  53).

distance( 7, 30,  34).
distance( 7, 31,  26).
distance( 7, 32,  39).
distance( 7, 33,  49).
distance( 7, 34,  30).
distance( 7, 35,  32).
distance( 7, 36,  51).
distance( 7, 37,  36).
distance( 7, 38,  38).
distance( 7, 39,  36).

distance( 7, 40,  33).
distance( 7, 41,  55).
distance( 7, 42,  61).

distance( 8,  9,   5).

distance( 8, 10,  24).
distance( 8, 11,  46).
distance( 8, 12,  51).
distance( 8, 13,  88).
distance( 8, 14, 124).
distance( 8, 15, 130).
distance( 8, 16, 104).
distance( 8, 17,  85).
distance( 8, 18, 117).
distance( 8, 19, 124).

distance( 8, 20, 105).
distance( 8, 21,  77).
distance( 8, 22,  60).
distance( 8, 23,  57).
distance( 8, 24,  28).
distance( 8, 25,  19).
distance( 8, 26,  29).
distance( 8, 27,  33).
distance( 8, 28,  49).
distance( 8, 29,  56).

distance( 8, 30,  38).
distance( 8, 31,  32).
distance( 8, 32,  44).
distance( 8, 33,  56).
distance( 8, 34,  39).
distance( 8, 35,  41).
distance( 8, 36,  60).
distance( 8, 37,  47).
distance( 8, 38,  48).
distance( 8, 39,  46).

distance( 8, 40,  40).
distance( 8, 41,  58).
distance( 8, 42,  61).

distance( 9, 10,  20).
distance( 9, 11,  41).
distance( 9, 12,  46).
distance( 9, 13,  84).
distance( 9, 14, 120).
distance( 9, 15, 125).
distance( 9, 16, 105).
distance( 9, 17,  86).
distance( 9, 18, 118).
distance( 9, 19, 128).

distance( 9, 20, 110).
distance( 9, 21,  84).
distance( 9, 22,  61).
distance( 9, 23,  59).
distance( 9, 24,  29).
distance( 9, 25,  21).
distance( 9, 26,  32).
distance( 9, 27,  36).
distance( 9, 28,  54).
distance( 9, 29,  61).

distance( 9, 30,  43).
distance( 9, 31,  36).
distance( 9, 32,  49).
distance( 9, 33,  60).
distance( 9, 34,  44).
distance( 9, 35,  46).
distance( 9, 36,  66).
distance( 9, 37,  52).
distance( 9, 38,  53).
distance( 9, 39,  51).

distance( 9, 40,  45).
distance( 9, 41,  63).
distance( 9, 42,  66).

distance(10, 11,  23).
distance(10, 12,  26).
distance(10, 13,  63).
distance(10, 14,  99).
distance(10, 15, 105).
distance(10, 16,  90).
distance(10, 17,  75).
distance(10, 18, 107).
distance(10, 19, 118).

distance(10, 20, 104).
distance(10, 21,  77).
distance(10, 22,  50).
distance(10, 23,  48).
distance(10, 24,  22).
distance(10, 25,  14).
distance(10, 26,  27).
distance(10, 27,  30).
distance(10, 28,  48).
distance(10, 29,  57).

distance(10, 30,  49).
distance(10, 31,  51).
distance(10, 32,  63).
distance(10, 33,  75).
distance(10, 34,  62).
distance(10, 35,  64).
distance(10, 36,  83).
distance(10, 37,  71).
distance(10, 38,  73).
distance(10, 39,  70).

distance(10, 40,  65).
distance(10, 41,  83).
distance(10, 42,  84).

distance(11, 12,  11).
distance(11, 13,  49).
distance(11, 14,  85).
distance(11, 15,  90).
distance(11, 16,  72).
distance(11, 17,  51).
distance(11, 18,  83).
distance(11, 19,  93).

distance(11, 20,  86).
distance(11, 21,  56).
distance(11, 22,  34).
distance(11, 23,  28).
distance(11, 24,  23).
distance(11, 25,  29).
distance(11, 26,  36).
distance(11, 27,  34).
distance(11, 28,  46).
distance(11, 29,  59).

distance(11, 30,  60).
distance(11, 31,  63).
distance(11, 32,  76).
distance(11, 33,  86).
distance(11, 34,  78).
distance(11, 35,  83).
distance(11, 36, 102).
distance(11, 37,  93).
distance(11, 38,  96).
distance(11, 39,  93).

distance(11, 40,  87).
distance(11, 41, 105).
distance(11, 42, 111).

distance(12, 13,  40).
distance(12, 14,  76).
distance(12, 15,  81).
distance(12, 16,  64).
distance(12, 17,  59).
distance(12, 18,  84).
distance(12, 19, 101).

distance(12, 20,  97).
distance(12, 21,  64).
distance(12, 22,  42).
distance(12, 23,  36).
distance(12, 24,  35).
distance(12, 25,  40).
distance(12, 26,  47).
distance(12, 27,  45).
distance(12, 28,  59).
distance(12, 29,  71).

distance(12, 30,  71).
distance(12, 31,  75).
distance(12, 32,  87).
distance(12, 33,  97).
distance(12, 34,  89).
distance(12, 35,  90).
distance(12, 36, 110).
distance(12, 37,  98).
distance(12, 38,  99).
distance(12, 39,  97).

distance(12, 40,  91).
distance(12, 41, 109).
distance(12, 42, 113).

distance(13, 14,  35).
distance(13, 15,  41).
distance(13, 16,  34).
distance(13, 17,  29).
distance(13, 18,  54).
distance(13, 19,  72).

distance(13, 20,  71).
distance(13, 21,  65).
distance(13, 22,  49).
distance(13, 23,  43).
distance(13, 24,  69).
distance(13, 25,  77).
distance(13, 26,  78).
distance(13, 27,  77).
distance(13, 28,  85).
distance(13, 29,  96).

distance(13, 30, 103).
distance(13, 31, 106).
distance(13, 32, 120).
distance(13, 33, 126).
distance(13, 34, 121).
distance(13, 35, 130).
distance(13, 36, 147).
distance(13, 37, 136).
distance(13, 38, 137).
distance(13, 39, 134).

distance(13, 40, 117).
distance(13, 41, 147).
distance(13, 42, 150).

distance(14, 15,  10).
distance(14, 16,  31).
distance(14, 17,  53).
distance(14, 18,  46).
distance(14, 19,  69).

distance(14, 20,  93).
distance(14, 21,  90).
distance(14, 22,  82).
distance(14, 23,  77).
distance(14, 24, 105).
distance(14, 25, 114).
distance(14, 26, 116).
distance(14, 27, 115).
distance(14, 28, 119).
distance(14, 29, 130).

distance(14, 30, 141).
distance(14, 31, 142).
distance(14, 32, 155).
distance(14, 33, 160).
distance(14, 34, 159).
distance(14, 35, 164).
distance(14, 36, 185).
distance(14, 37, 172).
distance(14, 38, 176).
distance(14, 39, 171).

distance(14, 40, 166).
distance(14, 41, 186).
distance(14, 42, 186).

distance(15, 16,  27).
distance(15, 17,  48).
distance(15, 18,  35).
distance(15, 19,  58).

distance(15, 20,  82).
distance(15, 21,  87).
distance(15, 22,  77).
distance(15, 23,  72).
distance(15, 24, 102).
distance(15, 25, 111).
distance(15, 26, 112).
distance(15, 27, 110).
distance(15, 28, 115).
distance(15, 29, 126).

distance(15, 30, 136).
distance(15, 31, 140).
distance(15, 32, 150).
distance(15, 33, 155).
distance(15, 34, 155).
distance(15, 35, 160).
distance(15, 36, 179).
distance(15, 37, 172).
distance(15, 38, 178).
distance(15, 39, 176).

distance(15, 40, 171).
distance(15, 41, 188).
distance(15, 42, 192).

distance(16, 17,  21).
distance(16, 18,  26).
distance(16, 19,  58).

distance(16, 20,  62).
distance(16, 21,  58).
distance(16, 22,  60).
distance(16, 23,  45).
distance(16, 24,  74).
distance(16, 25,  84).
distance(16, 26,  84).
distance(16, 27,  83).
distance(16, 28,  88).
distance(16, 29,  98).

distance(16, 30, 109).
distance(16, 31, 112).
distance(16, 32, 123).
distance(16, 33, 128).
distance(16, 34, 127).
distance(16, 35, 133).
distance(16, 36, 155).
distance(16, 37, 148).
distance(16, 38, 151).
distance(16, 39, 151).

distance(16, 40, 144).
distance(16, 41, 164).
distance(16, 42, 166).

distance(17, 18,  31).
distance(17, 19,  43).

distance(17, 20,  42).
distance(17, 21,  36).
distance(17, 22,  30).
distance(17, 23,  27).
distance(17, 24,  56).
distance(17, 25,  64).
distance(17, 26,  66).
distance(17, 27,  63).
distance(17, 28,  66).
distance(17, 29,  75).

distance(17, 30,  90).
distance(17, 31,  93).
distance(17, 32, 100).
distance(17, 33, 104).
distance(17, 34, 108).
distance(17, 35, 114).
distance(17, 36, 133).
distance(17, 37, 126).
distance(17, 38, 131).
distance(17, 39, 129).

distance(17, 40, 125).
distance(17, 41, 144).
distance(17, 42, 147).

distance(18, 19,  26).

distance(18, 20,  45).
distance(18, 21,  68).
distance(18, 22,  62).
distance(18, 23,  59).
distance(18, 24,  88).
distance(18, 25,  96).
distance(18, 26,  98).
distance(18, 27,  97).
distance(18, 28,  98).
distance(18, 29,  98).

distance(18, 30, 115).
distance(18, 31, 126).
distance(18, 32, 123).
distance(18, 33, 128).
distance(18, 34, 136).
distance(18, 35, 146).
distance(18, 36, 159).
distance(18, 37, 158).
distance(18, 38, 163).
distance(18, 39, 161).

distance(18, 40, 157).
distance(18, 41, 176).
distance(18, 42, 180).

distance(19, 20,  22).
distance(19, 21,  50).
distance(19, 22,  70).
distance(19, 23,  69).
distance(19, 24,  99).
distance(19, 25, 107).
distance(19, 26,  95).
distance(19, 27,  91).
distance(19, 28,  79).
distance(19, 29,  85).

distance(19, 30,  99).
distance(19, 31, 108).
distance(19, 32, 109).
distance(19, 33, 113).
distance(19, 34, 124).
distance(19, 35, 134).
distance(19, 36, 146).
distance(19, 37, 147).
distance(19, 38, 159).
distance(19, 39, 163).

distance(19, 40, 156).
distance(19, 41, 182).
distance(19, 42, 188).

distance(20, 21,  30).
distance(20, 22,  49).
distance(20, 23,  55).
distance(20, 24,  81).
distance(20, 25,  87).
distance(20, 26,  75).
distance(20, 27,  72).
distance(20, 28,  59).
distance(20, 29,  62).

distance(20, 30,  81).
distance(20, 31,  88).
distance(20, 32,  86).
distance(20, 33,  90).
distance(20, 34, 101).
distance(20, 35, 111).
distance(20, 36, 122).
distance(20, 37, 124).
distance(20, 38, 135).
distance(20, 39, 139).

distance(20, 40, 139).
distance(20, 41, 161).
distance(20, 42, 167).

distance(21, 22,  21).
distance(21, 23,  27).
distance(21, 24,  54).
distance(21, 25,  60).
distance(21, 26,  47).
distance(21, 27,  44).
distance(21, 28,  31).
distance(21, 29,  38).

distance(21, 30,  53).
distance(21, 31,  60).
distance(21, 32,  62).
distance(21, 33,  67).
distance(21, 34,  75).
distance(21, 35,  85).
distance(21, 36,  98).
distance(21, 37, 121).
distance(21, 38, 108).
distance(21, 39, 118).

distance(21, 40, 113).
distance(21, 41, 134).
distance(21, 42, 140).

distance(22, 23,   5).
distance(22, 24,  32).
distance(22, 25,  40).
distance(22, 26,  36).
distance(22, 27,  32).
distance(22, 28,  36).
distance(22, 29,  47).

distance(22, 30,  61).
distance(22, 31,  64).
distance(22, 32,  71).
distance(22, 33,  76).
distance(22, 34,  79).
distance(22, 35,  84).
distance(22, 36, 105).
distance(22, 37,  97).
distance(22, 38, 102).
distance(22, 39, 102).

distance(22, 40,  95).
distance(22, 41, 119).
distance(22, 42, 124).

distance(23, 24,  29).
distance(23, 25,  37).
distance(23, 26,  39).
distance(23, 27,  36).
distance(23, 28,  42).
distance(23, 29,  53).

distance(23, 30,  62).
distance(23, 31,  66).
distance(23, 32,  78).
distance(23, 33,  82).
distance(23, 34,  81).
distance(23, 35,  86).
distance(23, 36, 107).
distance(23, 37,  99).
distance(23, 38, 103).
distance(23, 39, 101).

distance(23, 40,  97).
distance(23, 41, 116).
distance(23, 42, 119).

distance(24, 25,   8).
distance(24, 26,  12).
distance(24, 27,   9).
distance(24, 28,  28).
distance(24, 29,  39).

distance(24, 30,  36).
distance(24, 31,  39).
distance(24, 32,  52).
distance(24, 33,  62).
distance(24, 34,  54).
distance(24, 35,  59).
distance(24, 36,  79).
distance(24, 37,  71).
distance(24, 38,  73).
distance(24, 39,  71).

distance(24, 40,  67).
distance(24, 41,  86).
distance(24, 42,  90).

distance(25, 26,  11).
distance(25, 27,  15).
distance(25, 28,  33).
distance(25, 29,  42).

distance(25, 30,  34).
distance(25, 31,  36).
distance(25, 32,  49).
distance(25, 33,  59).
distance(25, 34,  50).
distance(25, 35,  52).
distance(25, 36,  71).
distance(25, 37,  65).
distance(25, 38,  67).
distance(25, 39,  65).

distance(25, 40,  60).
distance(25, 41,  78).
distance(25, 42,  87).

distance(26, 27,   3).
distance(26, 28,  21).
distance(26, 29,  29).

distance(26, 30,  24).
distance(26, 31,  27).
distance(26, 32,  39).
distance(26, 33,  49).
distance(26, 34,  42).
distance(26, 35,  47).
distance(26, 36,  66).
distance(26, 37,  59).
distance(26, 38,  64).
distance(26, 39,  65).

distance(26, 40,  62).
distance(26, 41,  84).
distance(26, 42,  90).

distance(27, 28,  20).
distance(27, 29,  30).

distance(27, 30,  28).
distance(27, 31,  31).
distance(27, 32,  44).
distance(27, 33,  53).
distance(27, 34,  46).
distance(27, 35,  51).
distance(27, 36,  70).
distance(27, 37,  63).
distance(27, 38,  69).
distance(27, 39,  70).

distance(27, 40,  67).
distance(27, 41,  88).
distance(27, 42,  94).

distance(28, 29,  12).

distance(28, 30,  20).
distance(28, 31,  28).
distance(28, 32,  35).
distance(28, 33,  40).
distance(28, 34,  43).
distance(28, 35,  53).
distance(28, 36,  70).
distance(28, 37,  67).
distance(28, 38,  75).
distance(28, 39,  84).

distance(28, 40,  79).
distance(28, 41, 101).
distance(28, 42, 107).

distance(29, 30,  20).
distance(29, 31,  28).
distance(29, 32,  24).
distance(29, 33,  29).
distance(29, 34,  39).
distance(29, 35,  49).
distance(29, 36,  60).
distance(29, 37,  62).
distance(29, 38,  72).
distance(29, 39,  78).

distance(29, 40,  82).
distance(29, 41, 108).
distance(29, 42, 114).

distance(30, 31,   8).
distance(30, 32,  15).
distance(30, 33,  25).
distance(30, 34,  23).
distance(30, 35,  32).
distance(30, 36,  48).
distance(30, 37,  46).
distance(30, 38,  54).
distance(30, 39,  58).

distance(30, 40,  62).
distance(30, 41,  88).
distance(30, 42,  77).

distance(31, 32,  12).
distance(31, 33,  23).
distance(31, 34,  14).
distance(31, 35,  24).
distance(31, 36,  40).
distance(31, 37,  38).
distance(31, 38,  46).
distance(31, 39,  50).

distance(31, 40,  53).
distance(31, 41,  80).
distance(31, 42,  86).

distance(32, 33,  11).
distance(32, 34,  14).
distance(32, 35,  24).
distance(32, 36,  36).
distance(32, 37,  37).
distance(32, 38,  49).
distance(32, 39,  56).

distance(32, 40,  59).
distance(32, 41,  86).
distance(32, 42,  92).

distance(33, 34,  21).
distance(33, 35,  30).
distance(33, 36,  33).
distance(33, 37,  43).
distance(33, 38,  54).
distance(33, 39,  62).

distance(33, 40,  66).
distance(33, 41,  92).
distance(33, 42,  98).

distance(34, 35,   9).
distance(34, 36,  25).
distance(34, 37,  23).
distance(34, 38,  34).
distance(34, 39,  41).

distance(34, 40,  45).
distance(34, 41,  71).
distance(34, 42,  80).

distance(35, 36,  18).
distance(35, 37,  13).
distance(35, 38,  24).
distance(35, 39,  32).

distance(35, 40,  38).
distance(35, 41,  64).
distance(35, 42,  74).

distance(36, 37,  17).
distance(36, 38,  29).
distance(36, 39,  38).

distance(36, 40,  45).
distance(36, 41,  71).
distance(36, 42,  77).

distance(37, 38,  12).
distance(37, 39,  21).

distance(37, 40,  27).
distance(37, 41,  54).
distance(37, 42,  60).

distance(38, 39,   9).

distance(38, 40,  15).
distance(38, 41,  41).
distance(38, 42,  48).

distance(39, 40,   6).
distance(39, 41,  32).
distance(39, 42,  38).

distance(40, 41,  25).
distance(40, 42,  32).

distance(41, 42,   6).
