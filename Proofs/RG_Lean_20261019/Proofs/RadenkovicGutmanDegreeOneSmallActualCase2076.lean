/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2076 : Family 10 := level10.get ⟨468,by decide⟩
def sourceMap2076 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2076 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2076_checked : acceptsGraphIso
    (source (graph core2076) (root 10) 0 0) DegreeOneSmallSpectrum1195.graph sourceMap2076=true := by decide +kernel
theorem fusedMap2076_checked : acceptsGraphIso
    (fused (graph core2076) (root 10) 0 0) DegreeOneSmallSpectrum1189.graph fusedMap2076=true := by decide +kernel
theorem certified2076 : Certified (graph core2076) (root 10) 0 0 :=
  of_native_maps core2076 DegreeOneSmallSpectrum1195.graph DegreeOneSmallSpectrum1189.graph
    sourceMap2076 fusedMap2076 sourceMap2076_checked fusedMap2076_checked
    DegreeOneSmallComparisons.comparison2076
#print axioms sourceMap2076_checked
#print axioms fusedMap2076_checked
#print axioms certified2076
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
