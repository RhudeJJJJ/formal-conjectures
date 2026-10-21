/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2159 : Family 10 := level10.get ⟨622,by decide⟩
def sourceMap2159 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2159 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2159_checked : acceptsGraphIso
    (source (graph core2159) (root 10) 0 0) DegreeOneSmallSpectrum1814.graph sourceMap2159=true := by decide +kernel
theorem fusedMap2159_checked : acceptsGraphIso
    (fused (graph core2159) (root 10) 0 0) DegreeOneSmallSpectrum1194.graph fusedMap2159=true := by decide +kernel
theorem certified2159 : Certified (graph core2159) (root 10) 0 0 :=
  of_native_maps core2159 DegreeOneSmallSpectrum1814.graph DegreeOneSmallSpectrum1194.graph
    sourceMap2159 fusedMap2159 sourceMap2159_checked fusedMap2159_checked
    DegreeOneSmallComparisons.comparison2159
#print axioms sourceMap2159_checked
#print axioms fusedMap2159_checked
#print axioms certified2159
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
