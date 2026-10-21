/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1385 : Family 9 := level9.get ⟨137,by decide⟩
def sourceMap1385 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1385 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1385_checked : acceptsGraphIso
    (source (graph core1385) (root 9) 0 0) SmallGeFourSpectrum124.graph sourceMap1385=true := by decide +kernel
theorem fusedMap1385_checked : acceptsGraphIso
    (fused (graph core1385) (root 9) 0 0) SmallGeFourSpectrum093.graph fusedMap1385=true := by decide +kernel
theorem certified1385 : Certified (graph core1385) (root 9) 0 0 :=
  of_native_maps core1385 SmallGeFourSpectrum124.graph SmallGeFourSpectrum093.graph
    sourceMap1385 fusedMap1385 sourceMap1385_checked fusedMap1385_checked
    DegreeOneSmallComparisons.comparison1385
#print axioms sourceMap1385_checked
#print axioms fusedMap1385_checked
#print axioms certified1385
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
