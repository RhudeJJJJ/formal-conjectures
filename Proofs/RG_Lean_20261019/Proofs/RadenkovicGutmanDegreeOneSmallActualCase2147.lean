/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2147 : Family 10 := level10.get ⟨598,by decide⟩
def sourceMap2147 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2147 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2147_checked : acceptsGraphIso
    (source (graph core2147) (root 10) 0 0) DegreeOneSmallSpectrum1758.graph sourceMap2147=true := by decide +kernel
theorem fusedMap2147_checked : acceptsGraphIso
    (fused (graph core2147) (root 10) 0 0) DegreeOneSmallSpectrum1155.graph fusedMap2147=true := by decide +kernel
theorem certified2147 : Certified (graph core2147) (root 10) 0 0 :=
  of_native_maps core2147 DegreeOneSmallSpectrum1758.graph DegreeOneSmallSpectrum1155.graph
    sourceMap2147 fusedMap2147 sourceMap2147_checked fusedMap2147_checked
    DegreeOneSmallComparisons.comparison2147
#print axioms sourceMap2147_checked
#print axioms fusedMap2147_checked
#print axioms certified2147
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
