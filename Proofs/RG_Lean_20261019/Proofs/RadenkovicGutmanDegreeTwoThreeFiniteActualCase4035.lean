/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4035 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap4035 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,10,4,5,6,7,8,9] (sourceLabel 4 2 2 v)
def fusedMap4035 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap4035_checked : acceptsGraphIso
    (source (graph core4035) (root 4) 2 2) DegreeOneSmallSpectrum345.graph sourceMap4035=true := by decide +kernel
theorem fusedMap4035_checked : acceptsGraphIso
    (fused (graph core4035) (root 4) 2 2) DegreeOneSmallSpectrum166.graph fusedMap4035=true := by decide +kernel
theorem certified4035 : Certified (graph core4035) (root 4) 2 2 :=
  of_native_maps core4035 DegreeOneSmallSpectrum345.graph DegreeOneSmallSpectrum166.graph
    sourceMap4035 fusedMap4035 sourceMap4035_checked fusedMap4035_checked
    DegreeTwoThreeFiniteComparisons.comparison4035
#print axioms sourceMap4035_checked
#print axioms fusedMap4035_checked
#print axioms certified4035
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
