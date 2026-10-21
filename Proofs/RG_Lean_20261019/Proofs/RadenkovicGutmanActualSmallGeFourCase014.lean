/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core014 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap014 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 0 2 v)
def fusedMap014 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap014_checked : acceptsGraphIso
    (source (graph core014) (root 5) 0 2) SmallGeFourSpectrum020.graph
      sourceMap014=true := by decide +kernel
theorem fusedMap014_checked : acceptsGraphIso
    (fused (graph core014) (root 5) 0 2) SmallGeFourSpectrum022.graph
      fusedMap014=true := by decide +kernel
theorem certified014 : Certified (graph core014) (root 5) 0 2 :=
  of_native_maps core014 SmallGeFourSpectrum020.graph SmallGeFourSpectrum022.graph
    sourceMap014 fusedMap014 sourceMap014_checked fusedMap014_checked
    SmallGeFourComparisons.comparison014
#print axioms sourceMap014_checked
#print axioms fusedMap014_checked
#print axioms certified014
def sourceMap014swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,7,8,9,6] (sourceLabel 5 2 0 v)
def fusedMap014swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap014swap_checked : acceptsGraphIso
    (source (graph core014) (root 5) 2 0) SmallGeFourSpectrum020.graph
      sourceMap014swap=true := by decide +kernel
theorem fusedMap014swap_checked : acceptsGraphIso
    (fused (graph core014) (root 5) 2 0) SmallGeFourSpectrum022.graph
      fusedMap014swap=true := by decide +kernel
theorem certified014swap : Certified (graph core014) (root 5) 2 0 :=
  of_native_maps core014 SmallGeFourSpectrum020.graph SmallGeFourSpectrum022.graph
    sourceMap014swap fusedMap014swap sourceMap014swap_checked fusedMap014swap_checked
    SmallGeFourComparisons.comparison014
#print axioms sourceMap014swap_checked
#print axioms fusedMap014swap_checked
#print axioms certified014swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
