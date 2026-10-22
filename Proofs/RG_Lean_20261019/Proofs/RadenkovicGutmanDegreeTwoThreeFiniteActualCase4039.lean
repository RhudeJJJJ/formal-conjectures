/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4039 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap4039 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,11,5,6,7,8,9,10] (sourceLabel 5 2 2 v)
def fusedMap4039 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap4039_checked : acceptsGraphIso
    (source (graph core4039) (root 5) 2 2) DegreeOneSmallSpectrum765.graph sourceMap4039=true := by decide +kernel
theorem fusedMap4039_checked : acceptsGraphIso
    (fused (graph core4039) (root 5) 2 2) DegreeOneSmallSpectrum372.graph fusedMap4039=true := by decide +kernel
theorem certified4039 : Certified (graph core4039) (root 5) 2 2 :=
  of_native_maps core4039 DegreeOneSmallSpectrum765.graph DegreeOneSmallSpectrum372.graph
    sourceMap4039 fusedMap4039 sourceMap4039_checked fusedMap4039_checked
    DegreeTwoThreeFiniteComparisons.comparison4039
#print axioms sourceMap4039_checked
#print axioms fusedMap4039_checked
#print axioms certified4039
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
