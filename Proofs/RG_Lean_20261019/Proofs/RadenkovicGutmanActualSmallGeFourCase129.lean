/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core129 : Family 8 := level8.get ⟨239,by decide⟩
def sourceMap129 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 8 0 1 v)
def fusedMap129 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 0 1 v)
theorem sourceMap129_checked : acceptsGraphIso
    (source (graph core129) (root 8) 0 1) SmallGeFourSpectrum175.graph
      sourceMap129=true := by decide +kernel
theorem fusedMap129_checked : acceptsGraphIso
    (fused (graph core129) (root 8) 0 1) SmallGeFourSpectrum177.graph
      fusedMap129=true := by decide +kernel
theorem certified129 : Certified (graph core129) (root 8) 0 1 :=
  of_native_maps core129 SmallGeFourSpectrum175.graph SmallGeFourSpectrum177.graph
    sourceMap129 fusedMap129 sourceMap129_checked fusedMap129_checked
    SmallGeFourComparisons.comparison129
#print axioms sourceMap129_checked
#print axioms fusedMap129_checked
#print axioms certified129
def sourceMap129swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7,11] (sourceLabel 8 1 0 v)
def fusedMap129swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 1 0 v)
theorem sourceMap129swap_checked : acceptsGraphIso
    (source (graph core129) (root 8) 1 0) SmallGeFourSpectrum175.graph
      sourceMap129swap=true := by decide +kernel
theorem fusedMap129swap_checked : acceptsGraphIso
    (fused (graph core129) (root 8) 1 0) SmallGeFourSpectrum177.graph
      fusedMap129swap=true := by decide +kernel
theorem certified129swap : Certified (graph core129) (root 8) 1 0 :=
  of_native_maps core129 SmallGeFourSpectrum175.graph SmallGeFourSpectrum177.graph
    sourceMap129swap fusedMap129swap sourceMap129swap_checked fusedMap129swap_checked
    SmallGeFourComparisons.comparison129
#print axioms sourceMap129swap_checked
#print axioms fusedMap129swap_checked
#print axioms certified129swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
