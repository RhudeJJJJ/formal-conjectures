/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1729 : Family 9 := level9.get ⟨546,by decide⟩
def sourceMap1729 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1729 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1729_checked : acceptsGraphIso
    (source (graph core1729) (root 9) 0 0) SmallGeFourSpectrum212.graph sourceMap1729=true := by decide +kernel
theorem fusedMap1729_checked : acceptsGraphIso
    (fused (graph core1729) (root 9) 0 0) SmallGeFourSpectrum118.graph fusedMap1729=true := by decide +kernel
theorem certified1729 : Certified (graph core1729) (root 9) 0 0 :=
  of_native_maps core1729 SmallGeFourSpectrum212.graph SmallGeFourSpectrum118.graph
    sourceMap1729 fusedMap1729 sourceMap1729_checked fusedMap1729_checked
    DegreeOneSmallComparisons.comparison1729
#print axioms sourceMap1729_checked
#print axioms fusedMap1729_checked
#print axioms certified1729
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
