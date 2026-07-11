import Tests.Framework
import Tests.ScaffoldTests
import Tests.CoreTests
import Tests.BinaryTests
import Tests.ChecksumTests
import Tests.HuffmanTests
import Tests.NetpbmTests
import Tests.BmpTests
import Tests.DrawTests
import Tests.FontTests
import Tests.TransformTests
import Tests.FilterTests
import Tests.InflateTests
import Tests.DeflateTests
import Tests.ZlibTests
import Tests.LzwTests
import Tests.PngEncodeTests
import Tests.PngDecodeTests
import Tests.QoiTests
import Tests.QuantizeTests
import Tests.IOTests
import Tests.GifTests
import Tests.JpegTests
import Tests.TiffTests
import Tests.KernelTests
import Tests.ResizeTests
import Tests.RoundTripTests

/-!
# Test runner

Every suite is registered here once, at scaffold time — work packages fill
in their own suite file and never touch this one (no merge conflicts).
-/

def main (args : List String) : IO UInt32 :=
  Tests.runAll (args := args) [
    Tests.ScaffoldTests.suite,
    Tests.CoreTests.suite,
    Tests.BinaryTests.suite,
    Tests.ChecksumTests.suite,
    Tests.HuffmanTests.suite,
    Tests.NetpbmTests.suite,
    Tests.BmpTests.suite,
    Tests.DrawTests.suite,
    Tests.FontTests.suite,
    Tests.TransformTests.suite,
    Tests.FilterTests.suite,
    Tests.InflateTests.suite,
    Tests.DeflateTests.suite,
    Tests.ZlibTests.suite,
    Tests.LzwTests.suite,
    Tests.PngEncodeTests.suite,
    Tests.PngDecodeTests.suite,
    Tests.QoiTests.suite,
    Tests.QuantizeTests.suite,
    Tests.IOTests.suite,
    Tests.GifTests.suite,
    Tests.JpegTests.suite,
    Tests.TiffTests.suite,
    Tests.KernelTests.suite,
    Tests.ResizeTests.suite,
    Tests.RoundTripTests.suite
  ]
