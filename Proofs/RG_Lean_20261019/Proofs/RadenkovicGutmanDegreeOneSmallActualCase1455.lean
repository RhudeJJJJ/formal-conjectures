/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1455 : Family 9 := level9.get ⟨189,by decide⟩
def sourceMap1455 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1455 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1455_checked : acceptsGraphIso
    (source (graph core1455) (root 9) 0 0) DegreeOneSmallSpectrum693.graph sourceMap1455=true := by decide +kernel
theorem fusedMap1455_checked : acceptsGraphIso
    (fused (graph core1455) (root 9) 0 0) DegreeOneSmallSpectrum493.graph fusedMap1455=true := by decide +kernel
theorem certified1455 : Certified (graph core1455) (root 9) 0 0 :=
  of_native_maps core1455 DegreeOneSmallSpectrum693.graph DegreeOneSmallSpectrum493.graph
    sourceMap1455 fusedMap1455 sourceMap1455_checked fusedMap1455_checked
    DegreeOneSmallComparisons.comparison1455
#print axioms sourceMap1455_checked
#print axioms fusedMap1455_checked
#print axioms certified1455
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
