/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4485 : Family 10 := level10.get ⟨237,by decide⟩
def sourceMap4485 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4485 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4485_checked : acceptsGraphIso
    (source (graph core4485) (root 10) 2 2) DegreeTwoThreeSpectrum6331.graph sourceMap4485=true := by decide +kernel
theorem fusedMap4485_checked : acceptsGraphIso
    (fused (graph core4485) (root 10) 2 2) DegreeTwoThreeSpectrum5300.graph fusedMap4485=true := by decide +kernel
theorem certified4485 : Certified (graph core4485) (root 10) 2 2 :=
  of_native_maps core4485 DegreeTwoThreeSpectrum6331.graph DegreeTwoThreeSpectrum5300.graph
    sourceMap4485 fusedMap4485 sourceMap4485_checked fusedMap4485_checked
    DegreeTwoThreeFiniteComparisons.comparison4485
#print axioms sourceMap4485_checked
#print axioms fusedMap4485_checked
#print axioms certified4485
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
