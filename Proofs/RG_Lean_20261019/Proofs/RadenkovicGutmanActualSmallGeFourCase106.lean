/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core106 : Family 7 := level7.get ⟨114,by decide⟩
def sourceMap106 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11] (sourceLabel 7 0 2 v)
def fusedMap106 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap106_checked : acceptsGraphIso
    (source (graph core106) (root 7) 0 2) SmallGeFourSpectrum199.graph
      sourceMap106=true := by decide +kernel
theorem fusedMap106_checked : acceptsGraphIso
    (fused (graph core106) (root 7) 0 2) SmallGeFourSpectrum112.graph
      fusedMap106=true := by decide +kernel
theorem certified106 : Certified (graph core106) (root 7) 0 2 :=
  of_native_maps core106 SmallGeFourSpectrum199.graph SmallGeFourSpectrum112.graph
    sourceMap106 fusedMap106 sourceMap106_checked fusedMap106_checked
    SmallGeFourComparisons.comparison106
#print axioms sourceMap106_checked
#print axioms fusedMap106_checked
#print axioms certified106
def sourceMap106swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,9] (sourceLabel 7 2 0 v)
def fusedMap106swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap106swap_checked : acceptsGraphIso
    (source (graph core106) (root 7) 2 0) SmallGeFourSpectrum199.graph
      sourceMap106swap=true := by decide +kernel
theorem fusedMap106swap_checked : acceptsGraphIso
    (fused (graph core106) (root 7) 2 0) SmallGeFourSpectrum112.graph
      fusedMap106swap=true := by decide +kernel
theorem certified106swap : Certified (graph core106) (root 7) 2 0 :=
  of_native_maps core106 SmallGeFourSpectrum199.graph SmallGeFourSpectrum112.graph
    sourceMap106swap fusedMap106swap sourceMap106swap_checked fusedMap106swap_checked
    SmallGeFourComparisons.comparison106
#print axioms sourceMap106swap_checked
#print axioms fusedMap106swap_checked
#print axioms certified106swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
