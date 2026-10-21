/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1389 : Family 9 := level9.get ⟨139,by decide⟩
def sourceMap1389 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1389 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1389_checked : acceptsGraphIso
    (source (graph core1389) (root 9) 0 0) DegreeOneSmallSpectrum621.graph sourceMap1389=true := by decide +kernel
theorem fusedMap1389_checked : acceptsGraphIso
    (fused (graph core1389) (root 9) 0 0) DegreeOneSmallSpectrum400.graph fusedMap1389=true := by decide +kernel
theorem certified1389 : Certified (graph core1389) (root 9) 0 0 :=
  of_native_maps core1389 DegreeOneSmallSpectrum621.graph DegreeOneSmallSpectrum400.graph
    sourceMap1389 fusedMap1389 sourceMap1389_checked fusedMap1389_checked
    DegreeOneSmallComparisons.comparison1389
#print axioms sourceMap1389_checked
#print axioms fusedMap1389_checked
#print axioms certified1389
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
