/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2057 : Family 10 := level10.get ⟨431,by decide⟩
def sourceMap2057 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2057 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2057_checked : acceptsGraphIso
    (source (graph core2057) (root 10) 0 0) DegreeOneSmallSpectrum1185.graph sourceMap2057=true := by decide +kernel
theorem fusedMap2057_checked : acceptsGraphIso
    (fused (graph core2057) (root 10) 0 0) DegreeOneSmallSpectrum1511.graph fusedMap2057=true := by decide +kernel
theorem certified2057 : Certified (graph core2057) (root 10) 0 0 :=
  of_native_maps core2057 DegreeOneSmallSpectrum1185.graph DegreeOneSmallSpectrum1511.graph
    sourceMap2057 fusedMap2057 sourceMap2057_checked fusedMap2057_checked
    DegreeOneSmallComparisons.comparison2057
#print axioms sourceMap2057_checked
#print axioms fusedMap2057_checked
#print axioms certified2057
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
