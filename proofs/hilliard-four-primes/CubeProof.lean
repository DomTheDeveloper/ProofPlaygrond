import Mathlib

/-! Finite prime-witness certificate. This module uses Lean's kernel and core library. -/

namespace CubeWitness
abbrev Row := Nat × Nat × Nat × Nat

/-- A common multiple of all integers from 1 through 4096. -/
def modulus : Nat := 30775068816701134298207426969956249464889492250759610008953942871958345023607415651718561640076862588289151161014914885838383595000589437531779091217718444413042260933800586775731372356680018323349333639964179046087670924256844033023976357294465609837450896293470092363846597394119591147041820947728511577908597258937440448691028574113193082192256282521623141369722116564576291006772932683843223020535777443974782766685045588727737830062549515944486076320242513264645325050850314035151522103645363855180521430199812544536785080574799545414895316213153065707391507474649948494031013979774842329773328527619587273065023375841436788087361553872383524160912781058479973203647725738216832496930699453145954860671353600141323604350756466379670010161755529634798210656938394970456954147767894958883347543933508318081176447378021037038430137948930174739191815943316377457736015204434676547529016610820783455770257348481657283825396069451069788089106264394178683874382222775691961203063164077705582770820460075660712461568134253046293493355839884813875874365360136006362392826210010012899558680116246518407899801002969488044149110244972628209061248963893120367195235629751860866410741709407480985718287351558306349152284599607390566295904113504518699900753571671949913717879782134957489931053214662957559529015781388948439423308088586244536448614340485773410276639114149202697905398516429234210131052738474334737855097823779968757304304244220362723445581122327623605272661142224349931601167857126951880680263741187519638701863179829573543524703057358108643221224920065635288859939933713033060415960979338157107720469072980604510644806045341445027645345314190890888126597045288160250428514683552233600759289271101459214666203013436741790431180840659114316559267241245075997095302435263142400000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modulus_checked : (List.range 4096).all (fun i => modulus % (i + 1) == 0) = true := by decide +kernel

def checkPrime (p : Nat) : Bool :=
  if p ≤ 4096 then
    decide (2 ≤ p) && (List.range 63).all fun i => decide (p < (i+2)^2 ∨ p % (i+2) ≠ 0)
  else decide (p ≤ 4096^2 ∧ Nat.gcd p modulus = 1)

def checkRow (n : Nat) (w : Row) : Bool :=
  let (a,b,c,d) := w
  decide (n^3 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < (n+1)^3) &&
    checkPrime a && checkPrime b && checkPrime c && checkPrime d

private def checkRows (start : Nat) : List Row → Bool
  | [] => true
  | w :: ws => checkRow start w && checkRows (start+1) ws

private theorem rows_sound {ws : List Row} {start : Nat} (h : checkRows start ws = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start + ws.length) : ∃ w : Row, checkRow n w = true := by
  induction ws generalizing start with
  | nil => simp at hhi; omega
  | cons w ws ih =>
    obtain ⟨hw,hws⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : n = start
    · subst n; exact ⟨w, hw⟩
    · apply ih hws (by omega)
      simp at hhi; omega

private def rows1 : List Row := [
  (2, 3, 5, 7),
  (11, 13, 17, 19),
  (29, 31, 37, 41),
  (67, 71, 73, 79),
  (127, 131, 137, 139),
  (223, 227, 229, 233),
  (347, 349, 353, 359),
  (521, 523, 541, 547),
  (733, 739, 743, 751),
  (1009, 1013, 1019, 1021),
  (1361, 1367, 1373, 1381),
  (1733, 1741, 1747, 1753),
  (2203, 2207, 2213, 2221),
  (2749, 2753, 2767, 2777),
  (3389, 3391, 3407, 3413),
  (4099, 4111, 4127, 4129)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block1 : checkRows 1 rows1 = true := by decide +kernel

private def rows17 : List Row := [
  (4919, 4931, 4933, 4937),
  (5839, 5843, 5849, 5851),
  (6863, 6869, 6871, 6883),
  (8009, 8011, 8017, 8039),
  (9277, 9281, 9283, 9293),
  (10651, 10657, 10663, 10667),
  (12197, 12203, 12211, 12227),
  (13829, 13831, 13841, 13859),
  (15629, 15641, 15643, 15647),
  (17579, 17581, 17597, 17599),
  (19687, 19697, 19699, 19709),
  (21961, 21977, 21991, 21997),
  (24391, 24407, 24413, 24419),
  (27011, 27017, 27031, 27043),
  (29803, 29819, 29833, 29837),
  (32771, 32779, 32783, 32789)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block17 : checkRows 17 rows17 = true := by decide +kernel

private def rows33 : List Row := [
  (35951, 35963, 35969, 35977),
  (39313, 39317, 39323, 39341),
  (42899, 42901, 42923, 42929),
  (46663, 46679, 46681, 46687),
  (50671, 50683, 50707, 50723),
  (54877, 54881, 54907, 54917),
  (59333, 59341, 59351, 59357),
  (64007, 64013, 64019, 64033),
  (68927, 68947, 68963, 68993),
  (74093, 74099, 74101, 74131),
  (79531, 79537, 79549, 79559),
  (85193, 85199, 85201, 85213),
  (91127, 91129, 91139, 91141),
  (97367, 97369, 97373, 97379),
  (103837, 103841, 103843, 103867),
  (110597, 110603, 110609, 110623)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block33 : checkRows 33 rows33 = true := by decide +kernel

private def rows49 : List Row := [
  (117659, 117671, 117673, 117679),
  (125003, 125017, 125029, 125053),
  (132661, 132667, 132679, 132689),
  (140611, 140617, 140627, 140629),
  (148891, 148913, 148921, 148927),
  (157477, 157483, 157489, 157513),
  (166393, 166399, 166403, 166409),
  (175621, 175631, 175633, 175649),
  (185221, 185233, 185243, 185267),
  (195121, 195127, 195131, 195137),
  (205391, 205397, 205399, 205417),
  (216023, 216037, 216061, 216071),
  (226991, 227011, 227027, 227053),
  (238331, 238339, 238361, 238363),
  (250049, 250051, 250057, 250073),
  (262147, 262151, 262153, 262187)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block49 : checkRows 49 rows49 = true := by decide +kernel

private def rows65 : List Row := [
  (274627, 274661, 274667, 274679),
  (287501, 287503, 287537, 287549),
  (300779, 300787, 300799, 300809),
  (314441, 314453, 314467, 314491),
  (328511, 328513, 328519, 328543),
  (343019, 343037, 343051, 343061),
  (357913, 357967, 357977, 357983),
  (373273, 373291, 373297, 373301),
  (389023, 389027, 389029, 389041),
  (405227, 405239, 405241, 405247),
  (421891, 421907, 421913, 421943),
  (438979, 438983, 438989, 439007),
  (456539, 456553, 456557, 456559),
  (474557, 474569, 474571, 474581),
  (493043, 493049, 493067, 493093),
  (512009, 512011, 512021, 512047)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block65 : checkRows 65 rows65 = true := by decide +kernel

private def rows81 : List Row := [
  (531457, 531481, 531497, 531521),
  (551381, 551387, 551407, 551423),
  (571789, 571799, 571801, 571811),
  (592723, 592727, 592741, 592747),
  (614129, 614143, 614147, 614153),
  (636059, 636061, 636071, 636073),
  (658507, 658547, 658549, 658573),
  (681481, 681487, 681493, 681497),
  (704983, 704989, 704993, 704999),
  (729019, 729023, 729037, 729041),
  (753583, 753587, 753589, 753611),
  (778693, 778697, 778699, 778709),
  (804367, 804371, 804383, 804409),
  (830587, 830591, 830597, 830617),
  (857407, 857411, 857419, 857431),
  (884743, 884789, 884791, 884803)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block81 : checkRows 81 rows81 = true := by decide +kernel

private def rows97 : List Row := [
  (912727, 912763, 912773, 912797),
  (941201, 941207, 941209, 941221),
  (970303, 970313, 970351, 970391),
  (1000003, 1000033, 1000037, 1000039),
  (1030307, 1030349, 1030357, 1030361),
  (1061227, 1061251, 1061261, 1061273),
  (1092731, 1092733, 1092757, 1092779),
  (1124867, 1124869, 1124951, 1124957),
  (1157627, 1157641, 1157669, 1157671),
  (1191019, 1191031, 1191061, 1191077),
  (1225061, 1225067, 1225073, 1225079),
  (1259737, 1259743, 1259749, 1259759),
  (1295033, 1295051, 1295057, 1295069),
  (1331023, 1331039, 1331041, 1331051),
  (1367647, 1367687, 1367711, 1367713),
  (1404937, 1404959, 1404961, 1404973)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block97 : checkRows 97 rows97 = true := by decide +kernel

private def rows113 : List Row := [
  (1442899, 1442911, 1442921, 1442923),
  (1481551, 1481573, 1481603, 1481611),
  (1520879, 1520887, 1520903, 1520923),
  (1560901, 1560913, 1560953, 1560967),
  (1601617, 1601623, 1601627, 1601629),
  (1643039, 1643069, 1643077, 1643099),
  (1685171, 1685179, 1685207, 1685209),
  (1728017, 1728019, 1728043, 1728061),
  (1771607, 1771613, 1771633, 1771657),
  (1815859, 1815871, 1815881, 1815883),
  (1860869, 1860877, 1860893, 1860923),
  (1906627, 1906637, 1906643, 1906673),
  (1953151, 1953157, 1953163, 1953167),
  (2000381, 2000387, 2000389, 2000393),
  (2048413, 2048419, 2048429, 2048467),
  (2097169, 2097211, 2097223, 2097229)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block113 : checkRows 113 rows113 = true := by decide +kernel

private def rows129 : List Row := [
  (2146691, 2146693, 2146723, 2146733),
  (2197021, 2197043, 2197049, 2197087),
  (2248117, 2248123, 2248133, 2248139),
  (2300003, 2300017, 2300021, 2300029),
  (2352641, 2352643, 2352653, 2352661),
  (2406121, 2406133, 2406139, 2406149),
  (2460397, 2460407, 2460421, 2460431),
  (2515477, 2515517, 2515523, 2515529),
  (2571409, 2571421, 2571427, 2571449),
  (2628077, 2628083, 2628089, 2628103),
  (2685629, 2685649, 2685653, 2685667),
  (2744003, 2744017, 2744029, 2744039),
  (2803253, 2803259, 2803291, 2803303),
  (2863291, 2863303, 2863309, 2863313),
  (2924209, 2924213, 2924227, 2924231),
  (2985991, 2986003, 2986031, 2986037)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block129 : checkRows 129 rows129 = true := by decide +kernel

private def rows145 : List Row := [
  (3048629, 3048631, 3048653, 3048659),
  (3112141, 3112147, 3112237, 3112247),
  (3176533, 3176597, 3176609, 3176617),
  (3241801, 3241807, 3241811, 3241817),
  (3307973, 3308027, 3308057, 3308077),
  (3375007, 3375017, 3375019, 3375037),
  (3442963, 3442979, 3442987, 3442991),
  (3511817, 3511819, 3511841, 3511861),
  (3581579, 3581593, 3581597, 3581609),
  (3652279, 3652303, 3652333, 3652357),
  (3723893, 3723913, 3723931, 3723947),
  (3796451, 3796453, 3796469, 3796487),
  (3869917, 3869959, 3869989, 3869993),
  (3944329, 3944351, 3944359, 3944371),
  (4019689, 4019693, 4019707, 4019713),
  (4096013, 4096021, 4096033, 4096049)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block145 : checkRows 145 rows145 = true := by decide +kernel

private def rows161 : List Row := [
  (4173287, 4173311, 4173319, 4173329),
  (4251553, 4251563, 4251589, 4251601),
  (4330757, 4330763, 4330783, 4330819),
  (4410947, 4410949, 4410953, 4410961),
  (4492157, 4492171, 4492193, 4492211),
  (4574299, 4574327, 4574393, 4574407),
  (4657493, 4657537, 4657547, 4657553),
  (4741643, 4741673, 4741679, 4741717),
  (4826813, 4826831, 4826863, 4826867),
  (4913009, 4913011, 4913021, 4913063),
  (5000213, 5000251, 5000257, 5000263),
  (5088467, 5088511, 5088521, 5088529),
  (5177719, 5177723, 5177761, 5177771),
  (5268031, 5268077, 5268083, 5268091),
  (5359379, 5359427, 5359433, 5359447),
  (5451779, 5451791, 5451793, 5451799)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block161 : checkRows 161 rows161 = true := by decide +kernel

private def rows177 : List Row := [
  (5545273, 5545339, 5545357, 5545367),
  (5639759, 5639773, 5639797, 5639813),
  (5735357, 5735369, 5735393, 5735413),
  (5832007, 5832019, 5832049, 5832053),
  (5929747, 5929817, 5929841, 5929853),
  (6028571, 6028577, 6028579, 6028597),
  (6128491, 6128501, 6128503, 6128509),
  (6229507, 6229513, 6229523, 6229529),
  (6331669, 6331679, 6331691, 6331723),
  (6434861, 6434899, 6434921, 6434927),
  (6539209, 6539243, 6539263, 6539293),
  (6644681, 6644717, 6644753, 6644761),
  (6751271, 6751291, 6751307, 6751313),
  (6859003, 6859009, 6859031, 6859033),
  (6967897, 6967903, 6967937, 6967949),
  (7077893, 7077901, 7077907, 7077911)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block177 : checkRows 177 rows177 = true := by decide +kernel

private def rows193 : List Row := [
  (7189081, 7189097, 7189103, 7189123),
  (7301389, 7301401, 7301423, 7301431),
  (7414879, 7414889, 7414903, 7414909),
  (7529573, 7529603, 7529617, 7529659),
  (7645387, 7645403, 7645411, 7645423),
  (7762397, 7762423, 7762427, 7762429),
  (7880627, 7880641, 7880659, 7880671),
  (8000009, 8000017, 8000023, 8000033),
  (8120617, 8120641, 8120653, 8120659),
  (8242411, 8242439, 8242457, 8242459),
  (8365447, 8365457, 8365463, 8365471),
  (8489729, 8489743, 8489777, 8489807),
  (8615137, 8615149, 8615161, 8615177),
  (8741839, 8741861, 8741867, 8741911),
  (8869747, 8869759, 8869771, 8869781),
  (8998919, 8998921, 8998963, 8998987)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block193 : checkRows 193 rows193 = true := by decide +kernel

private def rows209 : List Row := [
  (9129331, 9129377, 9129401, 9129437),
  (9261013, 9261023, 9261041, 9261059),
  (9393949, 9393973, 9393977, 9393991),
  (9528131, 9528157, 9528163, 9528223),
  (9663629, 9663677, 9663679, 9663683),
  (9800363, 9800383, 9800387, 9800407),
  (9938377, 9938389, 9938393, 9938399),
  (10077721, 10077751, 10077763, 10077773),
  (10218323, 10218331, 10218349, 10218359),
  (10360241, 10360243, 10360247, 10360267),
  (10503461, 10503473, 10503491, 10503509),
  (10648021, 10648063, 10648091, 10648093),
  (10793941, 10793953, 10793977, 10794001),
  (10941059, 10941061, 10941067, 10941089),
  (11089577, 11089601, 11089607, 11089609),
  (11239427, 11239429, 11239447, 11239471)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block209 : checkRows 209 rows209 = true := by decide +kernel

private def rows225 : List Row := [
  (11390641, 11390647, 11390653, 11390669),
  (11543227, 11543249, 11543269, 11543293),
  (11697097, 11697109, 11697131, 11697167),
  (11852359, 11852369, 11852437, 11852459),
  (12008999, 12009031, 12009043, 12009047),
  (12167009, 12167017, 12167021, 12167033),
  (12326393, 12326417, 12326441, 12326443),
  (12487177, 12487187, 12487193, 12487201),
  (12649349, 12649391, 12649409, 12649447),
  (12812963, 12812981, 12812993, 12813023),
  (12977879, 12977927, 12977929, 12977947),
  (13144259, 13144267, 13144277, 13144291),
  (13312067, 13312081, 13312087, 13312093),
  (13481287, 13481309, 13481327, 13481329),
  (13651943, 13651973, 13651993, 13651999),
  (13824017, 13824023, 13824049, 13824059)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block225 : checkRows 225 rows225 = true := by decide +kernel

private def rows241 : List Row := [
  (13997537, 13997539, 13997551, 13997561),
  (14172493, 14172527, 14172533, 14172553),
  (14348909, 14348923, 14348951, 14348963),
  (14526793, 14526821, 14526839, 14526859),
  (14706127, 14706137, 14706143, 14706157),
  (14886943, 14886961, 14886967, 14886979),
  (15069233, 15069239, 15069251, 15069289),
  (15253009, 15253013, 15253027, 15253031),
  (15438251, 15438271, 15438289, 15438301),
  (15625007, 15625013, 15625019, 15625031),
  (15813257, 15813271, 15813283, 15813289),
  (16003021, 16003061, 16003067, 16003081),
  (16194287, 16194293, 16194301, 16194313),
  (16387081, 16387087, 16387093, 16387097),
  (16581391, 16581403, 16581431, 16581451)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block241 : checkRows 241 rows241 = true := by decide +kernel

theorem witnesses (n : Nat) (hn : 1 ≤ n) (h : n < 256) :
    ∃ w : Row, checkRow n w = true := by
  by_cases h17 : n < 17
  · exact rows_sound block1 n (by omega) (show n < 17 from h17)
  by_cases h33 : n < 33
  · exact rows_sound block17 n (by omega) (show n < 33 from h33)
  by_cases h49 : n < 49
  · exact rows_sound block33 n (by omega) (show n < 49 from h49)
  by_cases h65 : n < 65
  · exact rows_sound block49 n (by omega) (show n < 65 from h65)
  by_cases h81 : n < 81
  · exact rows_sound block65 n (by omega) (show n < 81 from h81)
  by_cases h97 : n < 97
  · exact rows_sound block81 n (by omega) (show n < 97 from h97)
  by_cases h113 : n < 113
  · exact rows_sound block97 n (by omega) (show n < 113 from h113)
  by_cases h129 : n < 129
  · exact rows_sound block113 n (by omega) (show n < 129 from h129)
  by_cases h145 : n < 145
  · exact rows_sound block129 n (by omega) (show n < 145 from h145)
  by_cases h161 : n < 161
  · exact rows_sound block145 n (by omega) (show n < 161 from h161)
  by_cases h177 : n < 177
  · exact rows_sound block161 n (by omega) (show n < 177 from h177)
  by_cases h193 : n < 193
  · exact rows_sound block177 n (by omega) (show n < 193 from h193)
  by_cases h209 : n < 209
  · exact rows_sound block193 n (by omega) (show n < 209 from h209)
  by_cases h225 : n < 225
  · exact rows_sound block209 n (by omega) (show n < 225 from h225)
  by_cases h241 : n < 241
  · exact rows_sound block225 n (by omega) (show n < 241 from h241)
  exact rows_sound block241 n (by omega) (show n < 256 from h)

end CubeWitness

/-! Translating the finite certificate into Mathlib's `Nat.Prime` predicate. -/

namespace CubePrimes
open Finset

private theorem checkPrime_sound {p : ℕ} (hc : CubeWitness.checkPrime p = true) : p.Prime := by
  unfold CubeWitness.checkPrime at hc
  split at hc
  next hp =>
    obtain ⟨hp2, htest⟩ := Bool.and_eq_true_iff.mp hc
    refine Nat.prime_def_le_sqrt.mpr ⟨of_decide_eq_true hp2, ?_⟩
    intro m hm hms hmp
    have hm2 : m ^ 2 ≤ p := by simpa [pow_two] using Nat.le_sqrt.mp hms
    have hm64 : m ≤ 64 := by nlinarith
    have hi : m-2 ∈ List.range 63 := List.mem_range.mpr (by omega)
    have hv := of_decide_eq_true (List.all_eq_true.mp htest (m-2) hi)
    rw [Nat.sub_add_cancel hm] at hv
    rcases hv with h | h
    · omega
    · exact h (Nat.mod_eq_zero_of_dvd hmp)
  next hp =>
    obtain ⟨hlim,hg⟩ := of_decide_eq_true hc
    by_contra hnp
    let m := p.minFac
    have hm : 2 ≤ m := Nat.minFac_prime (by omega : p ≠ 1) |>.two_le
    have hm2 : m^2 ≤ p := Nat.minFac_sq_le_self (by omega : 0 < p) hnp
    have hm4096 : m ≤ 4096 := by nlinarith
    have hi : m-1 ∈ List.range 4096 := List.mem_range.mpr (by omega)
    have ht := List.all_eq_true.mp CubeWitness.modulus_checked (m-1) hi
    have hdiv : m ∣ CubeWitness.modulus := by
      have he : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      rw [he] at ht
      exact Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp ht)
    have hone : m ∣ 1 := hg ▸ Nat.dvd_gcd (Nat.minFac_dvd p) hdiv
    have := Nat.le_of_dvd (by decide : 0 < 1) hone
    omega

private theorem row_sound {n : ℕ} {w : CubeWitness.Row} (h : CubeWitness.checkRow n w = true) :
    4 ≤ ((Ioo (n^3) ((n+1)^3)).filter Nat.Prime).card := by
  obtain ⟨a,b,c,d⟩ := w
  simp only [CubeWitness.checkRow, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hl,hab,hbc,hcd,hu⟩,ha⟩,hb⟩,hc⟩,hd⟩ := h
  have hs : ({a,b,c,d} : Finset ℕ) ⊆ (Ioo (n^3) ((n+1)^3)).filter Nat.Prime := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      apply mem_filter.mpr <;> exact ⟨mem_Ioo.mpr ⟨by omega, by omega⟩, checkPrime_sound (by assumption)⟩
  have hcard : ({a,b,c,d} : Finset ℕ).card = 4 := by
    simp [hab.ne, (hab.trans hbc).ne, ((hab.trans hbc).trans hcd).ne, hbc.ne, (hbc.trans hcd).ne, hcd.ne]
  simpa only [hcard] using card_le_card hs

theorem four_small (n : ℕ) (hn : 1 ≤ n) (h : n < 256) :
    4 ≤ ((Ioo (n^3) ((n+1)^3)).filter Nat.Prime).card := by
  obtain ⟨w,hw⟩ := CubeWitness.witnesses n hn h
  exact row_sound hw

end CubePrimes

/-! Four primes between consecutive cubes. Analytic part of the proof. -/


namespace CubePrimes
open Real Finset

/-- The constant is Schoenfeld's 1976 strict bound for Chebyshev's ψ. -/
abbrev SchoenfeldBound := ∀ x : ℝ, 73.2 ≤ x →
  |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)

private theorem log_sq_le {x : ℝ} (hx : 1 ≤ x) :
    log x ^ 2 ≤ (9/4 : ℝ) * √x := by
  have hx0 : 0 < x := by linarith
  let t := √(√x)
  have ht : 0 < t := sqrt_pos.2 (sqrt_pos.2 hx0)
  have he : (8/3 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hd := log_le_sub_one_of_pos (div_pos ht (exp_pos 1))
  rw [log_div ht.ne' (exp_pos 1).ne', log_exp] at hd
  have hmul : log t * exp 1 ≤ t := (le_div_iff₀ (exp_pos 1)).mp (by linarith)
  have hlogt : log t = log x / 4 := by
    dsimp [t]; rw [log_sqrt (sqrt_nonneg x), log_sqrt hx0.le]; ring
  have hl : 0 ≤ log t := by rw [hlogt]; positivity [log_nonneg hx]
  have hbound : log x ≤ (3/2 : ℝ) * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hl]
  have ht2 : t^2 = √x := sq_sqrt (sqrt_nonneg x)
  nlinarith [sq_le_sq' (by linarith [log_nonneg hx] : -((3/2 : ℝ) * t) ≤ log x) hbound]

private theorem sqrt_cube {x : ℝ} (hx : 0 ≤ x) : √(x^3) = x * √x := by
  rw [show x^3 = x^2*x by ring, sqrt_mul (sq_nonneg x), sqrt_sq hx]

private theorem cube_error (H : SchoenfeldBound) {x : ℝ} (hx : 5 ≤ x) :
    |Chebyshev.psi (x^3) - x^3| < (27/32 : ℝ)*x^2 := by
  have hx0 : 0 ≤ x := by linarith
  have h73 : (73.2 : ℝ) ≤ x^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hx 3
    norm_num at h ⊢; linarith
  refine (H (x^3) h73).trans_le ?_
  rw [sqrt_cube hx0, log_pow]
  apply (div_le_iff₀ (by positivity : 0 < 8 * π)).mpr
  have hb := mul_le_mul_of_nonneg_left (log_sq_le (x:=x) (by linarith))
    (mul_nonneg hx0 (sqrt_nonneg x))
  have hs : x * √x * √x = x^2 := by rw [mul_assoc, mul_self_sqrt hx0, pow_two]
  nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr pi_gt_three.le)]

private theorem higher_prime_powers {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 18 * √x := by
  have hz : 0 ≤ x := by linarith
  have h (k : ℕ) (hk : 2 ≤ k) :
      Chebyshev.psi (x ^ (k : ℝ)⁻¹) ≤ (log 4 + 4) * √x := by
    grw [Chebyshev.psi_le_const_mul_self (by positivity), sqrt_eq_rpow x]
    gcongr
    rw [← one_div (k : ℝ)]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)
  have hlog : log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hu := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := h 2 (by decide); have h3 := h 3 (by decide); have h5 := h 5 (by decide)
  push_cast at h2 h3 h5
  nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (sqrt_nonneg x)]

private theorem theta_growth (H : SchoenfeldBound) {x : ℝ} (hx : 256 ≤ x) :
    3 * log ((x+1)^3) < Chebyshev.theta ((x+1)^3) - Chebyshev.theta (x^3) := by
  let y := x+1
  have hy : 256 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hl := (abs_lt.mp (cube_error H (show 5 ≤ y by linarith))).1
  have hr := (abs_lt.mp (cube_error H (show 5 ≤ x by linarith))).2
  have hpow := higher_prime_powers (x := y^3) (by nlinarith [show (1:ℝ)^3 ≤ y^3 by gcongr; linarith])
  rw [sqrt_cube hy0] at hpow
  have hs16 : (16:ℝ) ≤ √y := (le_sqrt (by norm_num) hy0).2 (by linarith)
  have hs : 16 * √y ≤ y := by nlinarith [mul_nonneg (sqrt_nonneg y) (sub_nonneg.mpr hs16), sq_sqrt hy0]
  have hys := mul_le_mul_of_nonneg_left hs hy0
  have hlgy := log_le_sub_one_of_pos (show 0 < y by linarith)
  have h0 := Chebyshev.theta_le_psi (x^3)
  change 3 * log (y ^ 3) < Chebyshev.theta (y ^ 3) - Chebyshev.theta (x ^ 3)
  rw [log_pow]
  dsimp [y] at *
  nlinarith [mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x-256 by linarith)]

/-- The upper endpoint is included in the difference of two prime sums. Being a cube, it is composite. -/
private theorem theta_difference (n : ℕ) :
    Chebyshev.theta (((n+1)^3 : ℕ) : ℝ) - Chebyshev.theta ((n^3 : ℕ) : ℝ) =
      ∑ p ∈ (Ioo (n^3) ((n+1)^3)).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hn : n^3 ≤ (n+1)^3 := by gcongr; omega
  have hs : Nat.primesLE ((n+1)^3) \ Nat.primesLE (n^3) =
      (Ioo (n^3) ((n+1)^3)).filter Nat.Prime := by
    ext p
    simp only [mem_sdiff, Nat.mem_primesLE, mem_filter, mem_Ioo]
    have hc : ¬ ((n+1)^3).Prime := Nat.Prime.not_prime_pow (by decide : 2 ≤ 3)
    constructor
    · rintro ⟨⟨ha,hp⟩,hb⟩
      exact ⟨⟨lt_of_not_ge (fun hh ↦ hb ⟨hh,hp⟩), lt_of_le_of_ne ha (fun he ↦ hc (he ▸ hp))⟩, hp⟩
    · rintro ⟨⟨ha,hb⟩,hp⟩
      exact ⟨⟨hb.le,hp⟩, fun h ↦ ha.not_ge h.1⟩
  rw [← hs, ← sum_sdiff (Nat.primesLE_mono hn)]; simp

/-- Four distinct primes lie strictly inside each cube interval in the analytic range. -/
theorem four_large (H : SchoenfeldBound) (n : ℕ) (hn : 256 ≤ n) :
    4 ≤ ((Ioo (n^3) ((n+1)^3)).filter Nat.Prime).card := by
  let s := (Ioo (n^3) ((n+1)^3)).filter Nat.Prime
  by_contra! hbad
  change s.card < 4 at hbad
  have hcard : (s.card : ℝ) ≤ 3 := by exact_mod_cast (show s.card ≤ 3 by omega)
  have hsum : (∑ p ∈ s, log p) ≤ ∑ _p ∈ s, log (((n+1)^3 : ℕ) : ℝ) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
    exact log_le_log (by exact_mod_cast hpP.pos) (by exact_mod_cast (mem_Ioo.mp hpI).2.le)
  rw [sum_const, nsmul_eq_mul] at hsum
  have hlog : 0 ≤ log (((n+1)^3 : ℕ) : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ (n+1)^3 from Nat.one_le_iff_ne_zero.mpr (by positivity)))
  have hg := theta_growth H (x := (n:ℝ)) (by exact_mod_cast hn)
  have he := theta_difference n
  change _ = ∑ p ∈ s, _ at he
  push_cast at he hlog hsum
  linarith [mul_le_mul_of_nonneg_right hcard hlog]

end CubePrimes

namespace CubePrimes

/-- Schoenfeld's exact strict estimate suffices for all positive cubes. -/
theorem four_primes_of_schoenfeld
    (bound : ∀ x : ℝ, 73.2 ≤ x →
      |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi))
    (n : ℕ) (hn : 1 ≤ n) :
    4 ≤ ((Finset.Ioo (n^3) ((n+1)^3)).filter Nat.Prime).card := by
  by_cases h : n < 256
  · exact four_small n hn h
  · exact four_large bound n (Nat.le_of_not_gt h)

/-- The uniform lower bound is attained between 1 and 8. -/
theorem four_primes_at_one : ((Finset.Ioo (1^3) ((1+1)^3)).filter Nat.Prime).card = 4 := by
  decide +kernel

end CubePrimes
