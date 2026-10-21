/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2150 : Family 10 := level10.get ⟨604,by decide⟩
def sourceMap2150 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2150 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2150_checked : acceptsGraphIso
    (source (graph core2150) (root 10) 0 0) DegreeOneSmallSpectrum1714.graph sourceMap2150=true := by decide +kernel
theorem fusedMap2150_checked : acceptsGraphIso
    (fused (graph core2150) (root 10) 0 0) DegreeOneSmallSpectrum1175.graph fusedMap2150=true := by decide +kernel
theorem certified2150 : Certified (graph core2150) (root 10) 0 0 :=
  of_native_maps core2150 DegreeOneSmallSpectrum1714.graph DegreeOneSmallSpectrum1175.graph
    sourceMap2150 fusedMap2150 sourceMap2150_checked fusedMap2150_checked
    DegreeOneSmallComparisons.comparison2150
#print axioms sourceMap2150_checked
#print axioms fusedMap2150_checked
#print axioms certified2150
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
