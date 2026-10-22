/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5003 : Family 10 := level10.get ⟨1628,by decide⟩
def sourceMap5003 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap5003 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5003_checked : acceptsGraphIso
    (source (graph core5003) (root 10) 2 2) DegreeTwoThreeSpectrum7604.graph sourceMap5003=true := by decide +kernel
theorem fusedMap5003_checked : acceptsGraphIso
    (fused (graph core5003) (root 10) 2 2) DegreeTwoThreeSpectrum6191.graph fusedMap5003=true := by decide +kernel
theorem certified5003 : Certified (graph core5003) (root 10) 2 2 :=
  of_native_maps core5003 DegreeTwoThreeSpectrum7604.graph DegreeTwoThreeSpectrum6191.graph
    sourceMap5003 fusedMap5003 sourceMap5003_checked fusedMap5003_checked
    DegreeTwoThreeFiniteComparisons.comparison5003
#print axioms sourceMap5003_checked
#print axioms fusedMap5003_checked
#print axioms certified5003
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
