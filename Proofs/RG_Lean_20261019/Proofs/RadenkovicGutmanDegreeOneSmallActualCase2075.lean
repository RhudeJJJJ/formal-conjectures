/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2075 : Family 10 := level10.get ⟨467,by decide⟩
def sourceMap2075 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2075 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2075_checked : acceptsGraphIso
    (source (graph core2075) (root 10) 0 0) DegreeOneSmallSpectrum968.graph sourceMap2075=true := by decide +kernel
theorem fusedMap2075_checked : acceptsGraphIso
    (fused (graph core2075) (root 10) 0 0) DegreeOneSmallSpectrum967.graph fusedMap2075=true := by decide +kernel
theorem certified2075 : Certified (graph core2075) (root 10) 0 0 :=
  of_native_maps core2075 DegreeOneSmallSpectrum968.graph DegreeOneSmallSpectrum967.graph
    sourceMap2075 fusedMap2075 sourceMap2075_checked fusedMap2075_checked
    DegreeOneSmallComparisons.comparison2075
#print axioms sourceMap2075_checked
#print axioms fusedMap2075_checked
#print axioms certified2075
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
