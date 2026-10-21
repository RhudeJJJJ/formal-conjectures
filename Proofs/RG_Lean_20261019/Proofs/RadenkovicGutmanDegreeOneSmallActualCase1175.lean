/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1175 : Family 8 := level8.get ⟨214,by decide⟩
def sourceMap1175 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1175 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1175_checked : acceptsGraphIso
    (source (graph core1175) (root 8) 0 0) SmallGeFourSpectrum084.graph sourceMap1175=true := by decide +kernel
theorem fusedMap1175_checked : acceptsGraphIso
    (fused (graph core1175) (root 8) 0 0) SmallGeFourSpectrum048.graph fusedMap1175=true := by decide +kernel
theorem certified1175 : Certified (graph core1175) (root 8) 0 0 :=
  of_native_maps core1175 SmallGeFourSpectrum084.graph SmallGeFourSpectrum048.graph
    sourceMap1175 fusedMap1175 sourceMap1175_checked fusedMap1175_checked
    DegreeOneSmallComparisons.comparison1175
#print axioms sourceMap1175_checked
#print axioms fusedMap1175_checked
#print axioms certified1175
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
