/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core112 : Family 8 := level8.get ⟨160,by decide⟩
def sourceMap112 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap112 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap112_checked : acceptsGraphIso
    (source (graph core112) (root 8) 0 0) SmallGeFourSpectrum043.graph
      sourceMap112=true := by decide +kernel
theorem fusedMap112_checked : acceptsGraphIso
    (fused (graph core112) (root 8) 0 0) SmallGeFourSpectrum064.graph
      fusedMap112=true := by decide +kernel
theorem certified112 : Certified (graph core112) (root 8) 0 0 :=
  of_native_maps core112 SmallGeFourSpectrum043.graph SmallGeFourSpectrum064.graph
    sourceMap112 fusedMap112 sourceMap112_checked fusedMap112_checked
    SmallGeFourComparisons.comparison112
#print axioms sourceMap112_checked
#print axioms fusedMap112_checked
#print axioms certified112
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
