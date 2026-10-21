/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1433 : Family 9 := level9.get ⟨170,by decide⟩
def sourceMap1433 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1433 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1433_checked : acceptsGraphIso
    (source (graph core1433) (root 9) 0 0) DegreeOneSmallSpectrum720.graph sourceMap1433=true := by decide +kernel
theorem fusedMap1433_checked : acceptsGraphIso
    (fused (graph core1433) (root 9) 0 0) DegreeOneSmallSpectrum455.graph fusedMap1433=true := by decide +kernel
theorem certified1433 : Certified (graph core1433) (root 9) 0 0 :=
  of_native_maps core1433 DegreeOneSmallSpectrum720.graph DegreeOneSmallSpectrum455.graph
    sourceMap1433 fusedMap1433 sourceMap1433_checked fusedMap1433_checked
    DegreeOneSmallComparisons.comparison1433
#print axioms sourceMap1433_checked
#print axioms fusedMap1433_checked
#print axioms certified1433
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
