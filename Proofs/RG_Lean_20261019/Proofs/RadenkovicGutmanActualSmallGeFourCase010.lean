/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core010 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap010 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 4 2 2 v)
def fusedMap010 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap010_checked : acceptsGraphIso
    (source (graph core010) (root 4) 2 2) SmallGeFourSpectrum068.graph
      sourceMap010=true := by decide +kernel
theorem fusedMap010_checked : acceptsGraphIso
    (fused (graph core010) (root 4) 2 2) SmallGeFourSpectrum037.graph
      fusedMap010=true := by decide +kernel
theorem certified010 : Certified (graph core010) (root 4) 2 2 :=
  of_native_maps core010 SmallGeFourSpectrum068.graph SmallGeFourSpectrum037.graph
    sourceMap010 fusedMap010 sourceMap010_checked fusedMap010_checked
    SmallGeFourComparisons.comparison010
#print axioms sourceMap010_checked
#print axioms fusedMap010_checked
#print axioms certified010
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
