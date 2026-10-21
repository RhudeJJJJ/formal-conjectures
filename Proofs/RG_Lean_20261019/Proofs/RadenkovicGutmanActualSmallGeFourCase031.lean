/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core031 : Family 6 := level6.get ⟨36,by decide⟩
def sourceMap031 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,7,8,9,3,4,5,6,1,2] (sourceLabel 6 0 1 v)
def fusedMap031 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,7,8,9,4,5,6] (fusedLabel 6 0 1 v)
theorem sourceMap031_checked : acceptsGraphIso
    (source (graph core031) (root 6) 0 1) SmallGeFourSpectrum020.graph
      sourceMap031=true := by decide +kernel
theorem fusedMap031_checked : acceptsGraphIso
    (fused (graph core031) (root 6) 0 1) SmallGeFourSpectrum023.graph
      fusedMap031=true := by decide +kernel
theorem certified031 : Certified (graph core031) (root 6) 0 1 :=
  of_native_maps core031 SmallGeFourSpectrum020.graph SmallGeFourSpectrum023.graph
    sourceMap031 fusedMap031 sourceMap031_checked fusedMap031_checked
    SmallGeFourComparisons.comparison031
#print axioms sourceMap031_checked
#print axioms fusedMap031_checked
#print axioms certified031
def sourceMap031swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,7,8,9,3,4,5,1,2,6] (sourceLabel 6 1 0 v)
def fusedMap031swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,7,8,9,4,5,6] (fusedLabel 6 1 0 v)
theorem sourceMap031swap_checked : acceptsGraphIso
    (source (graph core031) (root 6) 1 0) SmallGeFourSpectrum020.graph
      sourceMap031swap=true := by decide +kernel
theorem fusedMap031swap_checked : acceptsGraphIso
    (fused (graph core031) (root 6) 1 0) SmallGeFourSpectrum023.graph
      fusedMap031swap=true := by decide +kernel
theorem certified031swap : Certified (graph core031) (root 6) 1 0 :=
  of_native_maps core031 SmallGeFourSpectrum020.graph SmallGeFourSpectrum023.graph
    sourceMap031swap fusedMap031swap sourceMap031swap_checked fusedMap031swap_checked
    SmallGeFourComparisons.comparison031
#print axioms sourceMap031swap_checked
#print axioms fusedMap031swap_checked
#print axioms certified031swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
