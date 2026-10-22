/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathCellCertificates
import Proofs.RadenkovicGutmanRationalPolynomialCell
namespace Gebendorfer.RadenkovicGutman.MeanPolynomialControl
open CoreQuotient PolynomialPathMap RationalComplexPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def as : List ℚ := [(36/49),(12/7),1]
def bs : List ℚ := [(-36/49),(-2340/343),(-365/49),(8/7),2]
def cs : List ℚ := [(-55/49),(5/7),1]
def es : List ℚ := [(55/49),(-723/343),(-267/49),(8/7),2]
def us : List ℚ := [0,0,(263218176/5764801),0,(8286021773584/13841287201),0,(660758570820/282475249),0,(21954974568/5764801),0,(344612644/117649),0,(2734944/2401),0,(10624/49),0,16]
def vs : List ℚ := [0,0,(263218176/5764801),0,(14539408/117649),0,(258660/2401),0,(1752/49),0,4]
def js : List ℚ := [0,0,0,0,(16120289240064/13841287201),0,(1294502819328/282475249),0,(38225763648/5764801),0,(523482048/117649),0,(3612240/2401),0,(12192/49),0,16]
def ns : List ℚ := [0,0,(4015008/117649),0,(161208/2401),0,(1524/49),0,4]
def sep : List ℚ := [0,0,(1637724/117649),0,(91236/2401),0,(1132/49),0,4]
def cu : Fin 17 → ℚ := ![(153541291022800/13841287201),(771739486566096/69206436005),(11636911313736916309/1038096540075000),(5459092631070627999923/484445052035000000),(203831802143164306185107/17993673361300000000),(860592629274452854465760161/75573428117460000000000),(317209112719990223171427551539/27710256976402000000000000),(1423555667180183130715116987503/123706504358937500000000000),(1717246871667692687723311212353893/148447805230725000000000000000),(17705384683424259791054887284443633/1522541592110000000000000000000),(32393227403108903019205582578858918241/2771025697640200000000000000000000),(487965460087412158992413451924253733/41523861603000000000000000000000),(1859932271538289460401526354729909962303/157444641911375000000000000000000000),(17978021860569255605671838926372737873727/1513890787609375000000000000000000000),(774539282997553378248333723534676853063041/64881033754687500000000000000000000000),(10381514931578444875977503626772492787775401/865080450062500000000000000000000000000),(1043613040551405098874177530448701690459368801/86508045006250000000000000000000000000000)]
def cv : Fin 17 → ℚ := ![(1825872080/5764801),(45787145386/144120025),(45927919240699/144120025000),(9213824976930653/28824005000000),(12014798547035347639/37471206500000000),(482069503163951443717/1498848260000000000),(531906756158509120037373/1648733086000000000000),(757872243460513223810979/2341950406250000000000),(20069339194956649871510763569/61827490725000000000000000),(536827728951926745076269245361/1648733086000000000000000000),(53847812608781455064535209904543/164873308600000000000000000000),(4910305321992923830470081984043/14988482600000000000000000000),(2462700556694025302736871011629/7494241300000000000000000000),(190020892595119578674956851793/576480100000000000000000000),(381210134327668663699425950201/1152960200000000000000000000),(382382067091688944915518377903/1152960200000000000000000000),(47944699309114536894549635801/144120025000000000000000000)]
def cj : Fin 17 → ℚ := ![(257407368966400/13841287201),(1293589411990252/69206436005),(1625219681183689533/86508045006250),(2286893036198848539589/121111263008750000),(426871385568835547760071/22492091701625000000),(60066329649657354481807749/3148892838227500000000),(6037223413398036121431532399/314889283822750000000000),(95353838892986334815904388081/4948260174357500000000000),(239598788376597476478532214354103/12370650435893750000000000000),(24081924019595468808905907225318817/1237065043589375000000000000000),(1694321898719164203886255540276933451/86594553051256250000000000000000),(1769302235631892863687901962209049849/89968366806500000000000000000000),(31120534962850594745651849590440118809743/1574446419113750000000000000000000000),(240608418993448420377961319667078648171523/12111126300875000000000000000000000000),(3454777133242006196478882608425606536975243/173016090012500000000000000000000000000),(8680953732377340428080645454287553569378963/432540225031250000000000000000000000000),(1745038340942796387295054420811848729131388801/86508045006250000000000000000000000000000)]
def cn : Fin 9 → ℚ := ![(16043920/117649),(1612560287/11764900),(1134539870227/8235430000),(57015878594839/411771500000),(28653136769559943/205885750000000),(230392746544045423/1647086000000000),(115783252451603897953/823543000000000000),(207809288205557851987/1470612500000000000),(41773656063873513766849/294122500000000000000)]
def ce : Fin 9 → ℚ := ![(9296816/117649),(467417679/5882450),(329006491447/4117715000),(16541548503121/205885750000),(4158323414482329/51471437500000),(669022526282795821/8235430000000000),(13454688112520501251/164708600000000000),(60398884888313029131/735306250000000000),(24293641744916672786849/294122500000000000000)]
def young : ℚ := (1/5)
def squareLower : ℚ := (611/500)
def payment : ℚ := (1/10)
theorem path_checked : GeneralPathPolynomials.accepts (13/7) 0 0 as bs cs es=true := by
  rw [GeneralPathPolynomials.accepts,decide_eq_true_eq]
  refine ⟨?_,?_,?_,?_⟩
  all_goals apply Polynomial.funext
  all_goals intro t
  all_goals norm_num [as,bs,cs,es,ofList,GeneralPathPolynomials.sourceSlope,
    GeneralPathPolynomials.sourceCenter,GeneralPathPolynomials.sourceOffset,
    GeneralPathPolynomials.fusedSlope,GeneralPathPolynomials.fusedCenter,
    GeneralPathPolynomials.fusedOffset,GeneralPathPolynomials.centerPoly,
    GeneralPathPolynomials.scalePoly,numPoly,denPoly,pointPoly,
    PathRecurrence.num,PathRecurrence.den,PathRecurrence.state]
  all_goals ring
theorem norms_checked : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep=true := by
  rw [RationalMobiusPolynomials.accepts,decide_eq_true_eq]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply Polynomial.funext
  all_goals intro t
  all_goals norm_num [as,bs,cs,es,us,vs,js,ns,sep,ofList,parts,normPolynomial,
    RationalMobiusPolynomials.U,RationalMobiusPolynomials.V,RationalMobiusPolynomials.J,
    RationalMobiusPolynomials.N,RationalMobiusPolynomials.E]
  all_goals ring
theorem coefficients_checked : ClassCellCertificates.accepts cu cv cj young squareLower=true := by decide +kernel
theorem logarithm_checked : RationalLog.accepts squareLower payment 0 40=true := by decide +kernel
theorem u_checked : RationalPolynomialCell.accepts us 1 (101/100) 16 cu=true := by
  rw [RationalPolynomialCell.accepts,decide_eq_true_eq]
  apply Polynomial.funext
  intro t
  norm_num [us,cu,ofList,RationalPolynomialCell.affine,RationalPolynomialCell.form,
    bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  all_goals ring
theorem v_checked : RationalPolynomialCell.accepts vs 1 (101/100) 16 cv=true := by
  rw [RationalPolynomialCell.accepts,decide_eq_true_eq]
  apply Polynomial.funext
  intro t
  norm_num [vs,cv,ofList,RationalPolynomialCell.affine,RationalPolynomialCell.form,
    bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  all_goals ring
theorem j_checked : RationalPolynomialCell.accepts js 1 (101/100) 16 cj=true := by
  rw [RationalPolynomialCell.accepts,decide_eq_true_eq]
  apply Polynomial.funext
  intro t
  norm_num [js,cj,ofList,RationalPolynomialCell.affine,RationalPolynomialCell.form,
    bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  all_goals ring
theorem n_checked : RationalPolynomialCell.accepts ns 1 (101/100) 8 cn=true := by
  rw [RationalPolynomialCell.accepts,decide_eq_true_eq]
  apply Polynomial.funext
  intro t
  norm_num [ns,cn,ofList,RationalPolynomialCell.affine,RationalPolynomialCell.form,
    bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  all_goals ring
theorem e_checked : RationalPolynomialCell.accepts sep 1 (101/100) 8 ce=true := by
  rw [RationalPolynomialCell.accepts,decide_eq_true_eq]
  apply Polynomial.funext
  intro t
  norm_num [sep,ce,ofList,RationalPolynomialCell.affine,RationalPolynomialCell.form,
    bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  all_goals ring
theorem n_positive : ∀ i, 0 < cn i := by decide +kernel
theorem e_positive : ∀ i, 0 < ce i := by decide +kernel
open scoped Classical
theorem actual_control {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u=1) (y : ℝ)
    (hy : y ∈ Set.Icc (1 : ℝ) (101/100)) :
    (payment : ℝ) ≤ MixedGraphIntegral.logarithm (source C u 0 0) (fused C u 0 0) ((13/7 : ℚ) : ℝ) y := by
  have hyp : 0 < y := by linarith only [hy.1]
  have hab : (1 : ℚ) < 101/100 := by norm_num
  have hcell : y ∈ Set.Icc ((1 : ℚ) : ℝ) ((101/100 : ℚ) : ℝ) := by
    convert hy using 1; norm_num
  apply GeneralPathCellCertificates.actual_log_lower (13/7) y hyp 0 0 as bs cs es us vs js ns sep
    path_checked norms_checked cu cv cj young squareLower payment 0 40 coefficients_checked logarithm_checked
    (fun i => Bernstein.basis 16 i ((y-((1 : ℚ) : ℝ))/(((101/100 : ℚ) : ℝ)-((1 : ℚ) : ℝ)))) ?_ ?_ ?_ ?_ ?_ ?_ C u hd
  · intro i
    exact Bernstein.basis_nonneg 16 i _ (RationalPolynomialCell.cell_coordinate 1 (101/100) hab y hcell)
  · exact RationalPolynomialCell.representation us 1 (101/100) 16 cu u_checked y hab
  · exact RationalPolynomialCell.representation vs 1 (101/100) 16 cv v_checked y hab
  · exact RationalPolynomialCell.representation js 1 (101/100) 16 cj j_checked y hab
  · exact RationalPolynomialCell.positive ns 1 (101/100) 8 cn n_checked n_positive hab y hcell
  · exact RationalPolynomialCell.positive sep 1 (101/100) 8 ce e_checked e_positive hab y hcell
theorem actual_mean14 {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u=1) (y : ℝ)
    (hy : y ∈ Set.Icc (1 : ℝ) (101/100)) :
    (payment : ℝ) ≤ MixedGraphIntegral.logarithm (source C u 0 0) (fused C u 0 0) (2-2/(14 : ℝ)) y := by
  convert actual_control C u hd y hy using 1; norm_num
#print axioms path_checked
#print axioms norms_checked
#print axioms coefficients_checked
#print axioms logarithm_checked
#print axioms u_checked
#print axioms v_checked
#print axioms j_checked
#print axioms n_checked
#print axioms e_checked
#print axioms n_positive
#print axioms e_positive
#print axioms actual_control
#print axioms actual_mean14
end Gebendorfer.RadenkovicGutman.MeanPolynomialControl
