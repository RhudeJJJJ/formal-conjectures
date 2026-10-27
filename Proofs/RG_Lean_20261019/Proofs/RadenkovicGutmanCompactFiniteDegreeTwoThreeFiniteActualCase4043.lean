/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4043 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap4043 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap4043 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap4043_checked : acceptsGraphIso
    (source (graph core4043) (root 5) 2 2) DegreeOneSmallSpectrum826.graph sourceMap4043=true := by decide +kernel
theorem fusedMap4043_checked : acceptsGraphIso
    (fused (graph core4043) (root 5) 2 2) DegreeOneSmallSpectrum434.graph fusedMap4043=true := by decide +kernel
theorem certified4043 : Certified (graph core4043) (root 5) 2 2 :=
  of_native_maps core4043 DegreeOneSmallSpectrum826.graph DegreeOneSmallSpectrum434.graph
    sourceMap4043 fusedMap4043 sourceMap4043_checked fusedMap4043_checked
    DegreeTwoThreeFiniteComparisons.comparison4043
#print axioms sourceMap4043_checked
#print axioms fusedMap4043_checked
#print axioms certified4043
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
