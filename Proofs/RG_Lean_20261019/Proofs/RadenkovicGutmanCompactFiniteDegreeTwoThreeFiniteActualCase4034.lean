/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4034 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap4034 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 3 2 2 v)
def fusedMap4034 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 2 2 v)
theorem sourceMap4034_checked : acceptsGraphIso
    (source (graph core4034) (root 3) 2 2) DegreeOneSmallSpectrum148.graph sourceMap4034=true := by decide +kernel
theorem fusedMap4034_checked : acceptsGraphIso
    (fused (graph core4034) (root 3) 2 2) DegreeOneSmallSpectrum086.graph fusedMap4034=true := by decide +kernel
theorem certified4034 : Certified (graph core4034) (root 3) 2 2 :=
  of_native_maps core4034 DegreeOneSmallSpectrum148.graph DegreeOneSmallSpectrum086.graph
    sourceMap4034 fusedMap4034 sourceMap4034_checked fusedMap4034_checked
    DegreeTwoThreeFiniteComparisons.comparison4034
#print axioms sourceMap4034_checked
#print axioms fusedMap4034_checked
#print axioms certified4034
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
