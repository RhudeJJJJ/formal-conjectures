/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2071 : Family 10 := level10.get ⟨455,by decide⟩
def sourceMap2071 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,1,0,8,9,10,11,12,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2071 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2071_checked : acceptsGraphIso
    (source (graph core2071) (root 10) 0 0) DegreeOneSmallSpectrum1475.graph sourceMap2071=true := by decide +kernel
theorem fusedMap2071_checked : acceptsGraphIso
    (fused (graph core2071) (root 10) 0 0) DegreeOneSmallSpectrum1463.graph fusedMap2071=true := by decide +kernel
theorem certified2071 : Certified (graph core2071) (root 10) 0 0 :=
  of_native_maps core2071 DegreeOneSmallSpectrum1475.graph DegreeOneSmallSpectrum1463.graph
    sourceMap2071 fusedMap2071 sourceMap2071_checked fusedMap2071_checked
    DegreeOneSmallComparisons.comparison2071
#print axioms sourceMap2071_checked
#print axioms fusedMap2071_checked
#print axioms certified2071
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
