/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core058 : Family 6 := level6.get ⟨47,by decide⟩
def sourceMap058 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4] (sourceLabel 6 1 1 v)
def fusedMap058 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap058_checked : acceptsGraphIso
    (source (graph core058) (root 6) 1 1) SmallGeFourSpectrum091.graph
      sourceMap058=true := by decide +kernel
theorem fusedMap058_checked : acceptsGraphIso
    (fused (graph core058) (root 6) 1 1) SmallGeFourSpectrum040.graph
      fusedMap058=true := by decide +kernel
theorem certified058 : Certified (graph core058) (root 6) 1 1 :=
  of_native_maps core058 SmallGeFourSpectrum091.graph SmallGeFourSpectrum040.graph
    sourceMap058 fusedMap058 sourceMap058_checked fusedMap058_checked
    SmallGeFourComparisons.comparison058
#print axioms sourceMap058_checked
#print axioms fusedMap058_checked
#print axioms certified058
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
