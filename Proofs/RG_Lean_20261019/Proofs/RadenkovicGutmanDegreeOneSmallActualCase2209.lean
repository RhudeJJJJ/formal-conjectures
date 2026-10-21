/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2209 : Family 10 := level10.get ⟨730,by decide⟩
def sourceMap2209 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2209 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2209_checked : acceptsGraphIso
    (source (graph core2209) (root 10) 0 0) DegreeOneSmallSpectrum1864.graph sourceMap2209=true := by decide +kernel
theorem fusedMap2209_checked : acceptsGraphIso
    (fused (graph core2209) (root 10) 0 0) DegreeOneSmallSpectrum1355.graph fusedMap2209=true := by decide +kernel
theorem certified2209 : Certified (graph core2209) (root 10) 0 0 :=
  of_native_maps core2209 DegreeOneSmallSpectrum1864.graph DegreeOneSmallSpectrum1355.graph
    sourceMap2209 fusedMap2209 sourceMap2209_checked fusedMap2209_checked
    DegreeOneSmallComparisons.comparison2209
#print axioms sourceMap2209_checked
#print axioms fusedMap2209_checked
#print axioms certified2209
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
