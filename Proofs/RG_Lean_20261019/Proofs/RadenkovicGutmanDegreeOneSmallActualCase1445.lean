/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1445 : Family 9 := level9.get ⟨180,by decide⟩
def sourceMap1445 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1445 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1445_checked : acceptsGraphIso
    (source (graph core1445) (root 9) 0 0) DegreeOneSmallSpectrum731.graph sourceMap1445=true := by decide +kernel
theorem fusedMap1445_checked : acceptsGraphIso
    (fused (graph core1445) (root 9) 0 0) DegreeOneSmallSpectrum468.graph fusedMap1445=true := by decide +kernel
theorem certified1445 : Certified (graph core1445) (root 9) 0 0 :=
  of_native_maps core1445 DegreeOneSmallSpectrum731.graph DegreeOneSmallSpectrum468.graph
    sourceMap1445 fusedMap1445 sourceMap1445_checked fusedMap1445_checked
    DegreeOneSmallComparisons.comparison1445
#print axioms sourceMap1445_checked
#print axioms fusedMap1445_checked
#print axioms certified1445
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
