/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2214 : Family 10 := level10.get ⟨739,by decide⟩
def sourceMap2214 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2214 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2214_checked : acceptsGraphIso
    (source (graph core2214) (root 10) 0 0) DegreeOneSmallSpectrum1866.graph sourceMap2214=true := by decide +kernel
theorem fusedMap2214_checked : acceptsGraphIso
    (fused (graph core2214) (root 10) 0 0) DegreeOneSmallSpectrum1366.graph fusedMap2214=true := by decide +kernel
theorem certified2214 : Certified (graph core2214) (root 10) 0 0 :=
  of_native_maps core2214 DegreeOneSmallSpectrum1866.graph DegreeOneSmallSpectrum1366.graph
    sourceMap2214 fusedMap2214 sourceMap2214_checked fusedMap2214_checked
    DegreeOneSmallComparisons.comparison2214
#print axioms sourceMap2214_checked
#print axioms fusedMap2214_checked
#print axioms certified2214
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
