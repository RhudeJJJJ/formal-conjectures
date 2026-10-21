/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2059 : Family 10 := level10.get ⟨434,by decide⟩
def sourceMap2059 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2059 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2059_checked : acceptsGraphIso
    (source (graph core2059) (root 10) 0 0) DegreeOneSmallSpectrum1190.graph sourceMap2059=true := by decide +kernel
theorem fusedMap2059_checked : acceptsGraphIso
    (fused (graph core2059) (root 10) 0 0) DegreeOneSmallSpectrum1512.graph fusedMap2059=true := by decide +kernel
theorem certified2059 : Certified (graph core2059) (root 10) 0 0 :=
  of_native_maps core2059 DegreeOneSmallSpectrum1190.graph DegreeOneSmallSpectrum1512.graph
    sourceMap2059 fusedMap2059 sourceMap2059_checked fusedMap2059_checked
    DegreeOneSmallComparisons.comparison2059
#print axioms sourceMap2059_checked
#print axioms fusedMap2059_checked
#print axioms certified2059
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
