/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core165 : Family 8 := level8.get ⟨283,by decide⟩
def sourceMap165 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,11,5,6] (sourceLabel 8 0 1 v)
def fusedMap165 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap165_checked : acceptsGraphIso
    (source (graph core165) (root 8) 0 1) SmallGeFourSpectrum231.graph
      sourceMap165=true := by decide +kernel
theorem fusedMap165_checked : acceptsGraphIso
    (fused (graph core165) (root 8) 0 1) SmallGeFourSpectrum167.graph
      fusedMap165=true := by decide +kernel
theorem certified165 : Certified (graph core165) (root 8) 0 1 :=
  of_native_maps core165 SmallGeFourSpectrum231.graph SmallGeFourSpectrum167.graph
    sourceMap165 fusedMap165 sourceMap165_checked fusedMap165_checked
    SmallGeFourComparisons.comparison165
#print axioms sourceMap165_checked
#print axioms fusedMap165_checked
#print axioms certified165
def sourceMap165swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6,11] (sourceLabel 8 1 0 v)
def fusedMap165swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap165swap_checked : acceptsGraphIso
    (source (graph core165) (root 8) 1 0) SmallGeFourSpectrum231.graph
      sourceMap165swap=true := by decide +kernel
theorem fusedMap165swap_checked : acceptsGraphIso
    (fused (graph core165) (root 8) 1 0) SmallGeFourSpectrum167.graph
      fusedMap165swap=true := by decide +kernel
theorem certified165swap : Certified (graph core165) (root 8) 1 0 :=
  of_native_maps core165 SmallGeFourSpectrum231.graph SmallGeFourSpectrum167.graph
    sourceMap165swap fusedMap165swap sourceMap165swap_checked fusedMap165swap_checked
    SmallGeFourComparisons.comparison165
#print axioms sourceMap165swap_checked
#print axioms fusedMap165swap_checked
#print axioms certified165swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
