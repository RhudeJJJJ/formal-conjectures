/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core052 : Family 6 := level6.get ⟨46,by decide⟩
def sourceMap052 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,7,8,9,10,3,4,5,6] (sourceLabel 6 1 1 v)
def fusedMap052 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap052_checked : acceptsGraphIso
    (source (graph core052) (root 6) 1 1) SmallGeFourSpectrum090.graph
      sourceMap052=true := by decide +kernel
theorem fusedMap052_checked : acceptsGraphIso
    (fused (graph core052) (root 6) 1 1) SmallGeFourSpectrum062.graph
      fusedMap052=true := by decide +kernel
theorem certified052 : Certified (graph core052) (root 6) 1 1 :=
  of_native_maps core052 SmallGeFourSpectrum090.graph SmallGeFourSpectrum062.graph
    sourceMap052 fusedMap052 sourceMap052_checked fusedMap052_checked
    SmallGeFourComparisons.comparison052
#print axioms sourceMap052_checked
#print axioms fusedMap052_checked
#print axioms certified052
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
