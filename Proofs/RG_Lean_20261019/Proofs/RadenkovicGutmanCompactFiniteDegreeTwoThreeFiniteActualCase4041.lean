/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4041 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap4041 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,10,11,4,5,6,7,8,9] (sourceLabel 5 2 2 v)
def fusedMap4041 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap4041_checked : acceptsGraphIso
    (source (graph core4041) (root 5) 2 2) DegreeOneSmallSpectrum822.graph sourceMap4041=true := by decide +kernel
theorem fusedMap4041_checked : acceptsGraphIso
    (fused (graph core4041) (root 5) 2 2) DegreeOneSmallSpectrum387.graph fusedMap4041=true := by decide +kernel
theorem certified4041 : Certified (graph core4041) (root 5) 2 2 :=
  of_native_maps core4041 DegreeOneSmallSpectrum822.graph DegreeOneSmallSpectrum387.graph
    sourceMap4041 fusedMap4041 sourceMap4041_checked fusedMap4041_checked
    DegreeTwoThreeFiniteComparisons.comparison4041
#print axioms sourceMap4041_checked
#print axioms fusedMap4041_checked
#print axioms certified4041
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
