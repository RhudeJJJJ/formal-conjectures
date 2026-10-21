/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1471 : Family 9 := level9.get ⟨206,by decide⟩
def sourceMap1471 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1471 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1471_checked : acceptsGraphIso
    (source (graph core1471) (root 9) 0 0) DegreeOneSmallSpectrum735.graph sourceMap1471=true := by decide +kernel
theorem fusedMap1471_checked : acceptsGraphIso
    (fused (graph core1471) (root 9) 0 0) DegreeOneSmallSpectrum509.graph fusedMap1471=true := by decide +kernel
theorem certified1471 : Certified (graph core1471) (root 9) 0 0 :=
  of_native_maps core1471 DegreeOneSmallSpectrum735.graph DegreeOneSmallSpectrum509.graph
    sourceMap1471 fusedMap1471 sourceMap1471_checked fusedMap1471_checked
    DegreeOneSmallComparisons.comparison1471
#print axioms sourceMap1471_checked
#print axioms fusedMap1471_checked
#print axioms certified1471
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
