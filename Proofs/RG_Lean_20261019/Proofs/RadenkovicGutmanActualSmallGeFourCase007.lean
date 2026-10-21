/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core007 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap007 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,3,4,5,6,1,2,7,8,9] (sourceLabel 4 1 2 v)
def fusedMap007 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap007_checked : acceptsGraphIso
    (source (graph core007) (root 4) 1 2) SmallGeFourSpectrum020.graph
      sourceMap007=true := by decide +kernel
theorem fusedMap007_checked : acceptsGraphIso
    (fused (graph core007) (root 4) 1 2) SmallGeFourSpectrum016.graph
      fusedMap007=true := by decide +kernel
theorem certified007 : Certified (graph core007) (root 4) 1 2 :=
  of_native_maps core007 SmallGeFourSpectrum020.graph SmallGeFourSpectrum016.graph
    sourceMap007 fusedMap007 sourceMap007_checked fusedMap007_checked
    SmallGeFourComparisons.comparison007
#print axioms sourceMap007_checked
#print axioms fusedMap007_checked
#print axioms certified007
def sourceMap007swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,3,4,5,6,7,8,9,1,2] (sourceLabel 4 2 1 v)
def fusedMap007swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap007swap_checked : acceptsGraphIso
    (source (graph core007) (root 4) 2 1) SmallGeFourSpectrum020.graph
      sourceMap007swap=true := by decide +kernel
theorem fusedMap007swap_checked : acceptsGraphIso
    (fused (graph core007) (root 4) 2 1) SmallGeFourSpectrum016.graph
      fusedMap007swap=true := by decide +kernel
theorem certified007swap : Certified (graph core007) (root 4) 2 1 :=
  of_native_maps core007 SmallGeFourSpectrum020.graph SmallGeFourSpectrum016.graph
    sourceMap007swap fusedMap007swap sourceMap007swap_checked fusedMap007swap_checked
    SmallGeFourComparisons.comparison007
#print axioms sourceMap007swap_checked
#print axioms fusedMap007swap_checked
#print axioms certified007swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
