/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4309 : Family 9 := level9.get ⟨379,by decide⟩
def sourceMap4309 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4309 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4309_checked : acceptsGraphIso
    (source (graph core4309) (root 9) 2 2) DegreeTwoThreeSpectrum4751.graph sourceMap4309=true := by decide +kernel
theorem fusedMap4309_checked : acceptsGraphIso
    (fused (graph core4309) (root 9) 2 2) DegreeTwoThreeSpectrum4315.graph fusedMap4309=true := by decide +kernel
theorem certified4309 : Certified (graph core4309) (root 9) 2 2 :=
  of_native_maps core4309 DegreeTwoThreeSpectrum4751.graph DegreeTwoThreeSpectrum4315.graph
    sourceMap4309 fusedMap4309 sourceMap4309_checked fusedMap4309_checked
    DegreeTwoThreeFiniteComparisons.comparison4309
#print axioms sourceMap4309_checked
#print axioms fusedMap4309_checked
#print axioms certified4309
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
