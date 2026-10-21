/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1331 : Family 9 := level9.get ⟨88,by decide⟩
def sourceMap1331 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1331 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1331_checked : acceptsGraphIso
    (source (graph core1331) (root 9) 0 0) DegreeOneSmallSpectrum432.graph sourceMap1331=true := by decide +kernel
theorem fusedMap1331_checked : acceptsGraphIso
    (fused (graph core1331) (root 9) 0 0) DegreeOneSmallSpectrum555.graph fusedMap1331=true := by decide +kernel
theorem certified1331 : Certified (graph core1331) (root 9) 0 0 :=
  of_native_maps core1331 DegreeOneSmallSpectrum432.graph DegreeOneSmallSpectrum555.graph
    sourceMap1331 fusedMap1331 sourceMap1331_checked fusedMap1331_checked
    DegreeOneSmallComparisons.comparison1331
#print axioms sourceMap1331_checked
#print axioms fusedMap1331_checked
#print axioms certified1331
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
