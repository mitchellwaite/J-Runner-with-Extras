using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;

namespace JRunner.Classes
{
    class xebuild
    {
        public enum XebuildError
        {
            none = 0,
            nocpukey,
            nofile,
            filemissing,
            nobinfile,
            nodash,
            noconsole,
            noinis,
            nobootloaders,
            wrongcpukey
        }

        private bool success = false;
        private string _cpukey;
        private variables.hacktypes _ttype;
        private string _dash;
        private consoles _ctype;
        private bool _audclamp;
        private bool _CR4;
        private bool _SMCP;
        private bool _CleanSMC;
        private bool _rgh3;
        private bool _bigffs;
        private bool _xdkbuild;
        private bool _fullDataClean;
        private bool _altoptions;
        private bool _DLpatches;
        private bool _includeLaunch;
        private bool _rjtag;
        private bool _nowrite;
        private bool _noava;
        private bool _clean;
        private bool _noreeb;
        private bool _xlusb;
        private bool _xlhdd;
        private bool _xlboth;
        private bool _jasperSbOverride;
        private Nand.PrivateN _nand;
        private List<string> _patches;

        // Methods for extracting the different sections of the input
        // xeBuild patch data
        //
        // xeBuild patch files contain multiple sections, with a DWORD of
        // 0xFFFFFFFF as the section terminator.
        //
        // 1st section is CB/CB_B/SB patches
        //
        // 2nd section is CD/SD patches
        //
        // 3rd section is the kernel patches, applied by the patching engine
        // in the SD to the kernel. This is the SE in a devkit image, or the
        // CE after CF/CG patching has taken place. XeBuild drops these as-is
        // in to the NAND image 
        //
        // The terminating 0xFFFFFFFF is included in each patch section
        //
        public static int getLengthOfPatchSection(byte[] bytes, int offset)
        {
            // Stop at the last DWORD of the byte array, no point searching further
            for (int i = offset; i < bytes.Length - 3; i++)
            {
                if (bytes[i] == 0xFF &&
                    bytes[i + 1] == 0xFF &&
                    bytes[i + 2] == 0xFF &&
                    bytes[i + 3] == 0xFF)
                {
                    return i + 4 - offset;
                }
            }

            return -1;
        }

        public static byte[] return2blPatchSet(byte[] xeBuildPatchData)
        {
            int sbPatchOffset = 0;
            int sbPatchLength = getLengthOfPatchSection(xeBuildPatchData, sbPatchOffset);

            if(sbPatchLength == -1)
            {
                return new byte[0];
            }

            return xeBuildPatchData.Take(sbPatchLength).ToArray();
        }

        public static byte[] return4blPatchSet(byte[] xeBuildPatchData)
        {
            int sbPatchOffset = 0;
            int sbPatchLength = getLengthOfPatchSection(xeBuildPatchData, sbPatchOffset);

            if (sbPatchLength == -1)
            {
                return new byte[0];
            }

            int sdPatchOffset = sbPatchOffset + sbPatchLength;
            int sdPatchLength = getLengthOfPatchSection(xeBuildPatchData, sdPatchOffset);

            if (sdPatchLength == -1)
            {
                return new byte[0];
            }

            return xeBuildPatchData.Skip(sdPatchOffset).Take(sdPatchLength).ToArray();
        }

        public static byte[] returnKernelHvPatchSet(byte[] xeBuildPatchData)
        {
            int sbPatchOffset = 0;
            int sbPatchLength = getLengthOfPatchSection(xeBuildPatchData, sbPatchOffset);

            if (sbPatchLength == -1)
            {
                return new byte[0];
            }

            int sdPatchOffset = sbPatchOffset + sbPatchLength;
            int sdPatchLength = getLengthOfPatchSection(xeBuildPatchData, sdPatchOffset);

            if (sdPatchLength == -1)
            {
                return new byte[0];
            }

            int khvPatchOffset = sdPatchOffset + sdPatchLength;
            int khvPatchLength = getLengthOfPatchSection(xeBuildPatchData, khvPatchOffset);

            if (khvPatchLength == -1)
            {
                return new byte[0];
            }

            return xeBuildPatchData.Skip(khvPatchOffset).Take(khvPatchLength).ToArray();
        }

        /// <summary>
        /// Prepares bootloader data for CRC calculation in the same way xeBuild
        /// does, e.g.
        /// - File is truncated to the DWORD size at 0xC
        /// - CB/CB_A/CB_B: fill with zeros from 0x10 for 0x30 bytes
        /// - SC/CD/SD/CE/SE/CG: fill with zeros from 0x10 for 0x10 bytes
        /// - CF: fill with zeros from 0x20 for 0x210 bytes
        /// 
        /// We don't need to look at the first byte for this, second
        /// byte is enough to tell if it's 2BL, 3BL, etc.
        /// 
        /// </summary>
        /// <param name="bl"></param>
        /// <returns></returns>
        private static byte[] prepBlForCrcCalc(byte[] bl)
        {
            int length = Oper.ByteArrayToInt(Oper.returnportion(bl, 0xC, 4));
            if ( bl[1] == 0x42 ) //CB, SB
            {
                for (int i = 0x10; i < 0x40; i++) bl[i] = 0x0;
            }
            else if ( bl[1] == 0x43 || // SC
                      bl[1] == 0x44 || // CD/SD
                      bl[1] == 0x45 || // CE/SE
                      bl[1] == 0x47 )  // CG
            {
                for (int i = 0x10; i < 0x20; i++) bl[i] = 0x0;
            }
            else if (bl[1] == 0x46) // CF
            {
                for (int i = 0x20; i < 0x230; i++) bl[i] = 0x0;
            }
            return Oper.returnportion(bl, 0, length);
        }

        /// <summary>
        /// Calculates the CRC32 of a bootloader in the same way xeBuild
        /// does for the purposes of integrity verification
        /// </summary>
        /// <param name="filename">Path to a BL file</param>
        /// <returns></returns>
        public static long calculateBlCrc(string filename)
        {
            return calculateBlCrc(File.ReadAllBytes(filename));
        }

        /// <summary>
        /// Calculates the CRC32 of a bootloader in the same way xeBuild
        /// does for the purposes of integrity verification
        /// </summary>
        /// <param name="blData">Byte buffer containing BL data</param>
        /// <returns></returns>
        public static long calculateBlCrc(byte[] blData)
        {
            byte[] processedBl = prepBlForCrcCalc(blData);

            crc32 crc = new crc32();

            return crc.CRC(processedBl);
        }

        public static byte[] patchBootloader(byte[] blData, byte[] patchData)
        {
            // xeBuild patch file format is the following:
            //
            // DWORD patch address
            // DWORD patch size
            // patch bytes
            //
            // repeated until an address of 0xFFFFFFFF is found
            Stream s = new MemoryStream(patchData);

            byte[] addressBytes = new byte[4];
            UInt32 address = 0;

            byte[] lengthBytes = new byte[4];
            UInt32 length = 0;

            byte[] patchSectionBytes = { };

            while(0 != s.Read(addressBytes, 0, 4))
            {
                address = BitConverter.ToUInt32(addressBytes.Reverse().ToArray(), 0);

                if (addressBytes[0] == 0xFF &&
                    addressBytes[1] == 0xFF &&
                    addressBytes[2] == 0xFF &&
                    addressBytes[3] == 0xFF)
                {
                    // We've found the terminating 0xFF, stop looping
                    break;
                }

                s.Read(lengthBytes, 0, 4);
                length = BitConverter.ToUInt32(lengthBytes.Reverse().ToArray(), 0) * 4;

                Array.Resize(ref patchSectionBytes, (int)length);
                s.Read(patchSectionBytes, 0, (int)length);

                // If the patch address and length would make us run off 
                // the end of the buffer we need to resize the buffer to fit.
                if (address + length > blData.Length)
                {
                    Array.Resize(ref blData, (int)(address + length));
                }

                Buffer.BlockCopy(patchSectionBytes, 0, blData, (int)address, (int)length);
            }

            // We've finished patching the bootloader. In case the patch made it an odd size
            // extend it to the nearest multiple of 0x10 bytes.
            int paddedLen = (blData.Length + 0xF) & ~0xF;

            if(paddedLen > blData.Length)
            {
                Array.Resize(ref blData, paddedLen);
            }

            // Set the size of the bootloader at 0xC 
            byte[] sizeBytes = BitConverter.GetBytes(paddedLen).Reverse().ToArray();
            Buffer.BlockCopy(sizeBytes, 0, blData, 0xC, 4);

            // We're all done!
            return blData;
        }

        public void loadvariables(string cpukey, variables.hacktypes ttype, string dash, consoles ctype, List<string> patches, Nand.PrivateN nand, bool altoptions, bool DLpatches, bool includeLaunch, bool audclamp, bool rjtag, bool cleansmc, bool cr4, bool smcp, bool rgh3, bool bigffs, bool xdkbuild, bool xlusb, bool xlhdd, bool xlboth, bool fullDataClean, bool jasperSbOverride)
        {
            this._cpukey = cpukey;
            this._ttype = ttype;
            this._dash = dash;
            this._ctype = ctype;
            this._patches = patches;
            this._nand = nand;
            this._altoptions = altoptions;
            this._DLpatches = DLpatches;
            this._includeLaunch = includeLaunch;
            this._audclamp = audclamp;
            this._rjtag = rjtag;
            this._CleanSMC = cleansmc;
            this._CR4 = cr4;
            this._SMCP = smcp;
            this._rgh3 = rgh3;
            this._bigffs = bigffs;
            this._xdkbuild = xdkbuild;
            this._xlusb = xlusb;
            this._xlhdd = xlhdd;
            this._xlboth = xlboth;
            this._fullDataClean = fullDataClean;
            this._jasperSbOverride = jasperSbOverride;
        }

        public List<int> getCBs()
        {
            List<int> cbs = new List<int>();
            string[] ommit = { "version", "security", "flashfs" };
            foreach (string s in parse_ini.getlabels(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\_" + _ttype + ".ini")))
            {
                if (!ommit.Contains(s) && s.Contains(_ctype.Ini))
                {
                    int cb;
                    if (int.TryParse(s.Replace(_ctype.Ini + "bl_", ""), out cb)) cbs.Add(cb);
                }
            }
            //int cba;
            //string normalc = (parse_ini.parselabel(Path.Combine(variables.pathforit, @"xeBuild\" + _dash + @"\_" + _ttype + ".ini"), _ctype.Ini + "bl")[0]);
            //string normalcb = normalc.Substring(normalc.IndexOf("_") + 1, normalc.IndexOf(".") - normalc.IndexOf("_") - 1);
            //if (int.TryParse(normalcb, out cba)) cbs.Add(cba);

            return cbs;
        }

        void copySMC()
        {
            if (_ttype == variables.hacktypes.jtag && !File.Exists(Path.Combine(variables.xepath, "SMC.bin")))
            {
                if (_ctype.ID == 7 || _ctype.ID == 8)
                {
                    File.Copy(variables.xepath + "SMCx.bin", variables.xepath + "SMC.bin", true);
                }
                else
                {
                    if (_audclamp) File.Copy(variables.xepath + "SMCaud.bin", variables.xepath + "SMC.bin", true);
                    else File.Copy(variables.xepath + "SMCfzj.bin", variables.xepath + "SMC.bin", true);
                }

                if (_rjtag)
                {
                    File.WriteAllBytes(variables.xepath + "SMC.bin", Nand.Nand.patch_SMC((File.ReadAllBytes(variables.xepath + "SMC.bin"))));
                }
                variables.copiedSMC = true;
            }
            else if (_ttype != variables.hacktypes.jtag && _CleanSMC)
            {
                if (_ctype.ID == 1 || _ctype.ID == 12)
                {
                    File.Copy(variables.xepath + "TRINITY_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 2 || _ctype.ID == 14)
                {
                    File.Copy(variables.xepath + "FALCON_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 3 || _ctype.ID == 13)
                {
                    File.Copy(variables.xepath + "ZEPHYR_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 4 || _ctype.ID == 5 || _ctype.ID == 6)
                {
                    File.Copy(variables.xepath + "JASPER_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 7 || _ctype.ID == 8)
                {
                    File.Copy(variables.xepath + "XENON_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 9 ||_ctype.ID == 10 || _ctype.ID == 11)
                {
                    File.Copy(variables.xepath + "CORONA_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 15 ||_ctype.ID == 16 || _ctype.ID == 17)
                {
                    File.Copy(variables.xepath + "WINCHESTER_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                variables.copiedSMC = true;
            }
            else if ((_ttype == variables.hacktypes.glitch2 || _ttype == variables.hacktypes.glitch2m) && _CR4)
            {
                if (_ctype.ID == 1 || _ctype.ID == 12)
                {
                    File.Copy(variables.xepath + "TRINITY_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 2 || _ctype.ID == 3 || _ctype.ID == 13 || _ctype.ID == 14)
                {
                    File.Copy(variables.xepath + "FALCON_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 4 || _ctype.ID == 5 || _ctype.ID == 6)
                {
                    File.Copy(variables.xepath + "JASPER_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 9 || _ctype.ID == 10 || _ctype.ID == 11)
                {
                    File.Copy(variables.xepath + "CORONA_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                variables.copiedSMC = true;
            }
            else if ((_ttype == variables.hacktypes.glitch2 || _ttype == variables.hacktypes.glitch2m) && _SMCP)
            {
                if (_ctype.ID == 1 || _ctype.ID == 12)
                {
                    File.Copy(variables.xepath + "TRINITY_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 2 || _ctype.ID == 3 || _ctype.ID == 13 || _ctype.ID == 14)
                {
                    File.Copy(variables.xepath + "FALCON_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 4 || _ctype.ID == 5 || _ctype.ID == 6)
                {
                    File.Copy(variables.xepath + "JASPER_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 7 || _ctype.ID == 8)
                {
                    File.Copy(variables.xepath + "XENON_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 9 || _ctype.ID == 10 || _ctype.ID == 11)
                {
                    File.Copy(variables.xepath + "CORONA_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                variables.copiedSMC = true;
            }
            else
            {
                variables.copiedSMC = false;
            }
        }
        void copySMCcustom()
        {
            if (_ttype == variables.hacktypes.jtag)
            {
                if (_ctype.ID == 7 || _ctype.ID == 8)
                {
                    File.Copy(variables.xepath + "SMCx.bin", variables.xepath + "SMC.bin", true);
                }
                else
                {
                    if (_audclamp) File.Copy(variables.xepath + "SMCaud.bin", variables.xepath + "SMC.bin", true);
                    else File.Copy(variables.xepath + "SMCfzj.bin", variables.xepath + "SMC.bin", true);
                }

                if (_rjtag)
                {
                    File.WriteAllBytes(variables.xepath + "SMC.bin", Nand.Nand.patch_SMC((File.ReadAllBytes(variables.xepath + "SMC.bin"))));
                }
                variables.copiedSMC = true;
            }
            else if (_ttype != variables.hacktypes.jtag && _CleanSMC)
            {
                if (_ctype.ID == 1 || _ctype.ID == 12)
                {
                    File.Copy(variables.xepath + "TRINITY_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 2 || _ctype.ID == 14)
                {
                    File.Copy(variables.xepath + "FALCON_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 3 || _ctype.ID == 13)
                {
                    File.Copy(variables.xepath + "ZEPHYR_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 4 || _ctype.ID == 5 || _ctype.ID == 6)
                {
                    File.Copy(variables.xepath + "JASPER_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 7 || _ctype.ID == 8)
                {
                    File.Copy(variables.xepath + "XENON_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 9 || _ctype.ID == 10 || _ctype.ID == 11)
                {
                    File.Copy(variables.xepath + "CORONA_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 15 || _ctype.ID == 16 || _ctype.ID == 17)
                {
                    File.Copy(variables.xepath + "WINCHESTER_CLEAN.bin", variables.xepath + "SMC.bin", true);
                }
                variables.copiedSMC = true;
            }
            else if ((_ttype == variables.hacktypes.glitch2 || _ttype == variables.hacktypes.glitch2m) && _CR4)
            {
                if (_ctype.ID == 1 || _ctype.ID == 12)
                {
                    File.Copy(variables.xepath + "TRINITY_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 2 || _ctype.ID == 3 || _ctype.ID == 13 || _ctype.ID == 14)
                {
                    File.Copy(variables.xepath + "FALCON_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 4 || _ctype.ID == 5 || _ctype.ID == 6)
                {
                    File.Copy(variables.xepath + "JASPER_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 9 || _ctype.ID == 10 || _ctype.ID == 11)
                {
                    File.Copy(variables.xepath + "CORONA_CR4.bin", variables.xepath + "SMC.bin", true);
                }
                variables.copiedSMC = true;
            }
            else if ((_ttype == variables.hacktypes.glitch2 || _ttype == variables.hacktypes.glitch2m) && _SMCP)
            {
                if (_ctype.ID == 1 || _ctype.ID == 12)
                {
                    File.Copy(variables.xepath + "TRINITY_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 2 || _ctype.ID == 3 || _ctype.ID == 13 || _ctype.ID == 14)
                {
                    File.Copy(variables.xepath + "FALCON_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 4 || _ctype.ID == 5 || _ctype.ID == 6)
                {
                    File.Copy(variables.xepath + "JASPER_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 7 || _ctype.ID == 8)
                {
                    File.Copy(variables.xepath + "XENON_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                else if (_ctype.ID == 9 || _ctype.ID == 10 || _ctype.ID == 11)
                {
                    File.Copy(variables.xepath + "CORONA_SMC+.bin", variables.xepath + "SMC.bin", true);
                }
                variables.copiedSMC = true;
            }
            else
            {
                variables.copiedSMC = false;
            }
        }

        private void copyXLUsb()
        {
            if (File.Exists(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_usb\xam.xex")))
            {
                if (File.Exists(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex")))
                {
                    File.Move(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex"), Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex.tmp"));
                }

                File.Copy(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_usb\xam.xex"), Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex"), true);

                string buildIni = Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\_" + variables.ttyp.ToString() + ".ini");
                string xlUsbIni = Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_usb\_" + variables.ttyp.ToString() + ".ini");
                if (File.Exists(xlUsbIni))
                {
                    if (File.Exists(buildIni))
                    {
                        File.Move(buildIni, buildIni + ".tmp");
                    }

                    File.Copy(xlUsbIni, buildIni, true);
                }

                variables.copiedXLDrive = true;
            }
            else
            {
                variables.copiedXLDrive = false;
            }
        }

        private void copyXLHdd()
        {
            if (File.Exists(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_hdd\xam.xex")))
            {
                if (File.Exists(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex")))
                {
                    File.Move(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex"), Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex.tmp"));
                }

                File.Copy(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_hdd\xam.xex"), Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex"), true);

                string buildIni = Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\_" + variables.ttyp.ToString() + ".ini");
                string xlHddIni = Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_hdd\_" + variables.ttyp.ToString() + ".ini");
                if (File.Exists(xlHddIni))
                {
                    if (File.Exists(buildIni))
                    {
                        File.Move(buildIni, buildIni + ".tmp");
                    }

                    File.Copy(xlHddIni, buildIni, true);
                }

                variables.copiedXLDrive = true;
            }
            else
            {
                variables.copiedXLDrive = false;
            }
        }

        private void copyXLBoth()
        {
            if (File.Exists(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_both\xam.xex")))
            {
                if (File.Exists(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex")))
                {
                    File.Move(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex"), Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex.tmp"));
                }

                File.Copy(Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_both\xam.xex"), Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xam.xex"), true);

                string buildIni = Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\_" + variables.ttyp.ToString() + ".ini");
                string xlBothIni = Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\xl_both\_" + variables.ttyp.ToString() + ".ini");
                if (File.Exists(xlBothIni))
                {
                    if (File.Exists(buildIni))
                    {
                        File.Move(buildIni, buildIni + ".tmp");
                    }

                    File.Copy(xlBothIni, buildIni, true);
                }

                variables.copiedXLDrive = true;
            }
            else
            {
                variables.copiedXLDrive = false;
            }
        }

        void checkDashLaunch()
        {
            if (_DLpatches && _includeLaunch)
            {
                if (!File.Exists(Path.Combine(variables.launchpath, _dash + @"\launch.ini")))
                {
                    if (File.Exists(Path.Combine(variables.launchpath, "launch.ini")))
                        System.IO.File.Copy(Path.Combine(variables.launchpath, "launch.ini"), Path.Combine(variables.launchpath, _dash + @"\launch.ini"), true);
                    else if (File.Exists(Path.Combine(variables.launchpath, "launch_default.ini")))
                        System.IO.File.Copy(Path.Combine(variables.launchpath, @"launch_default.ini"), Path.Combine(variables.launchpath, _dash + @"\launch.ini"), true);
                }
            }
            edittheini();
        }
        void edittheini()
        {
            if (variables.debugMode) Console.WriteLine(_dash);
            foreach (variables.hacktypes type in Enum.GetValues(typeof(variables.hacktypes)))
            {
                if (type == variables.hacktypes.retail || type == variables.hacktypes.nothing) continue;
                string file = Path.Combine(variables.rootfolder, @"xeBuild\" + _dash + @"\_" + type + ".ini");
                string[] writepatches = { @"..\launch.xex", @"..\lhelper.xex", @"..\launch.ini" };
                string[] writepatches2 = { @"..\launch.xex", @"..\lhelper.xex" };
                string[] empty = { };

                if (File.Exists(file))
                {
                    if (_DLpatches)
                    {
                        parse_ini.edit_ini(file, _includeLaunch ? writepatches : writepatches2, empty);
                    }
                    else
                    {
                        parse_ini.edit_ini(file, empty, writepatches);
                    }
                }
                else if (variables.debugMode) Console.WriteLine("Couldn't add dashlaunch patches to {0}", file);
            }
        }
        void savekvinfo(string savefile)
        {
            try
            {
                if (!_nand.ok) return;
                TextWriter tw = new StreamWriter(savefile);
                tw.WriteLine("*******************************************");
                tw.WriteLine("*******************************************");
                string console_type = _ctype.Text;
                tw.WriteLine("Console Type: {0}", console_type);
                tw.WriteLine("");
                tw.WriteLine("Cpu Key: {0}", _cpukey);
                tw.WriteLine("");
                tw.WriteLine("KV Type: {0}", _nand.ki.kvtype.Replace("0", ""));
                tw.WriteLine("");
                tw.WriteLine("MFR Date: {0}", _nand.ki.mfdate);
                tw.WriteLine("");
                tw.WriteLine("Console ID: {0}", _nand.ki.consoleid);
                tw.WriteLine("");
                tw.WriteLine("Serial: {0}", _nand.ki.serial);
                tw.WriteLine("");
                string region = "";
                if (_nand.ki.region == "02FE") region = "PAL/EU";
                else if (_nand.ki.region == "00FF") region = "NTSC/US";
                else if (_nand.ki.region == "01FE") region = "NTSC/JAP";
                else if (_nand.ki.region == "01FF") region = "NTSC/JAP";
                else if (_nand.ki.region == "01FC") region = "NTSC/KOR";
                else if (_nand.ki.region == "0101") region = "NTSC/HK";
                else if (_nand.ki.region == "0201") region = "PAL/AUS";
                else if (_nand.ki.region == "7FFF") region = "DEVKIT";
                tw.WriteLine("Region: {0} | {1}", _nand.ki.region, region);
                tw.WriteLine("");
                tw.WriteLine("Osig: {0}", _nand.ki.osig);
                tw.WriteLine("");
                tw.WriteLine("DVD Key: {0}", _nand.ki.dvdkey);
                tw.WriteLine("");
                tw.WriteLine("*******************************************");
                tw.WriteLine("*******************************************");
                tw.Close();
                Console.WriteLine("KV Info saved to file");
            }
            catch (Exception ex) { if (variables.debugMode) Console.WriteLine(ex.ToString()); Console.WriteLine("Failed"); Console.WriteLine(""); }
        }

        XebuildError doSomeChecks()
        {
            if (string.IsNullOrEmpty(_cpukey)) return XebuildError.nocpukey;

            if (_ctype.ID == -1) return XebuildError.noconsole;
            if (_dash.Equals("")) return XebuildError.nodash;
            string ini = (variables.launchpath + @"\" + _dash + @"\_" + _ttype + ".ini");

            // Type overrides, check doSomeChecks() if changing
            string boardtype = _ctype.Ini;

            if (_jasperSbOverride && (boardtype == "xenon" || boardtype == "zephyr" || boardtype == "falcon"))
            {
                // For the purposes of this check, we need to verify that there's a [jasperbl]
                // section in the ini. We don't need to override to jaspersb here.
                boardtype = "jasper";
            }

            string ctypebtldr = boardtype + "bl";
            if (!File.Exists(ini)) return XebuildError.noinis;
            if (!parse_ini.getlabels(ini).Contains(ctypebtldr)) return XebuildError.nobootloaders;

            return XebuildError.none;
        }
        void moveOptions()
        {
            if (_altoptions)
            {
                Console.WriteLine("Using edited settings");
                File.Copy(Path.Combine(variables.rootfolder, @"xebuild\options_edited.ini"), Path.Combine(variables.rootfolder, @"xebuild\data\options.ini"), true);
            }
            else
            {
                File.Copy(Path.Combine(variables.rootfolder, @"xebuild\options.ini"), Path.Combine(variables.rootfolder, @"xebuild\data\options.ini"), true);
            }

            // Don't patch the SMC reset limit if it's not a glitch
            // type image. JTAG doesn't reset the processor
            // and DevGL/Devkit/Testkit/Retail images boot directly
            // in to the kernel so if it takes more than one try
            // and the SMC is resetting, something is wrong and
            // we should be getting a red ring of some sort
            if( ! (_ttype == variables.hacktypes.glitch||
                   _ttype == variables.hacktypes.glitch2||
                   _ttype == variables.hacktypes.glitch2m) )
            {
                string[] dontPatchSmc = { "patchsmc=false" };
                string[] delete = { };
                parse_ini.edit_ini(Path.Combine(variables.rootfolder, @"xeBuild\data\options.ini"), dontPatchSmc, delete);
            }

        }

        public XebuildError createxebuild(bool custom)
        {
            XebuildError result = XebuildError.none;
            result = doSomeChecks();
            if (result != XebuildError.none) return result;
            moveOptions();
            if (variables.changeldv != 0)
            {
                string cfldv = "cfldv=" + variables.highldv.ToString();
                string[] edit = { cfldv };
                string[] delete = { };
                parse_ini.edit_ini(Path.Combine(variables.rootfolder, @"xeBuild\data\options.ini"), edit, delete);
            }

            Console.WriteLine("XeBuild Initialized");
            if (!custom) copySMC();
            else copySMCcustom();

            if (_xlusb) copyXLUsb();
            else if (_xlhdd) copyXLHdd();
            else if (_xlboth) copyXLBoth();

            variables.fullDataClean = _fullDataClean;

            checkDashLaunch();

            if (variables.changeldv != 0)
            {
                string cfldv = "cfldv=" + variables.highldv.ToString();
                string[] edit = { cfldv };
                string[] delete = { };
                parse_ini.edit_ini(Path.Combine(variables.rootfolder, @"xeBuild\data\options.ini"), edit, delete);
            }

            Console.WriteLine("Kernel Selected: {0}", _dash);

            variables.xefolder = Path.Combine(Directory.GetParent(variables.outfolder).FullName, _nand.ki.serial);
            if (variables.debugMode) Console.WriteLine("outfolder: {0}", variables.xefolder);
            if (!Directory.Exists(variables.xefolder)) Directory.CreateDirectory(variables.xefolder);
            File.WriteAllText(System.IO.Path.Combine(variables.xefolder, variables.cpukeypath), _cpukey);
            savekvinfo(Path.Combine(variables.xefolder, "KV_Info.txt"));
            if (variables.changeldv != 0) variables.changeldv = 2;

            return result;
        }

        private bool postBuildActionsAreRequired()
        {
            //
            // So far, the following image types require post-build actions
            // any others should be added here to prevent errors and file conflicts
            //
            // 1) XDKBuild glitch2m images (we need to inject the SC)
            // 2) Any type of RGH3 image
            //

            if( (_xdkbuild && _ttype == variables.hacktypes.glitch2m) || _rgh3)
            {
                return true;
            }
            else
            {
                return false;
            }
        }

        public void build()
        {
            success = false;
            System.Diagnostics.Process pProcess = new System.Diagnostics.Process();
            pProcess.StartInfo.FileName = variables.rootfolder + @"\xeBuild\xeBuild.exe";
            string arguments = "";
            string boardtype = _ctype.XeBuild;
            string[] iniFileContentsBackup = { };

            if (_jasperSbOverride)
            {
                // For the purposes of this check, we need to force the board type to jaspersb
                // or jaspersb64 so XeBuild produces an XSB image with the jasper bootloaders.
                // Make sure to update doSomeChecks if this changes.
                if (boardtype == "xenon" || boardtype == "zephyr" || boardtype == "falcon")
                {
                    boardtype = "jaspersb";
                }
                else if (boardtype == "xenon64" || boardtype == "zephyr64" || boardtype == "falcon64")
                {
                    boardtype = "jaspersb64";
                }
            }

            arguments = "-t " + _ttype;

            // For consoles with a big enough flashfs, use a different ini
            // with the entire flashfs contained within
            if (_xdkbuild)
            {
                if (boardtype == "jasperbb") // requires bigffs
                {
                    arguments += " -c " + "jasperbigffs -i flash";
                }
                else if (boardtype == "trinitybb") // requires bigffs
                {
                    arguments += " -c " + "trinitybigffs -i flash";
                }
                else if (boardtype == "coronabb") // requires bigffs
                {
                    arguments += " -c " + "coronabigffs -i flash";
                }
                else if (boardtype == "winchesterbb") // requires bigffs
                {
                    arguments += " -c " + "winchesterbigffs -i flash";
                }
                else if (boardtype == "corona4g"     ||
                         boardtype == "winchester4g" ||
                         boardtype == "xenon64"      ||
                         boardtype == "zephyr64"     ||
                         boardtype == "falcon64"     ||
                         boardtype == "jaspersb64" )
                {
                    arguments += " -c " + boardtype + " -i flash";
                }
                else // no bigffs!
                {
                    arguments += " -c " + boardtype;
                }
            }
            else if (_bigffs)
            {
                if (boardtype == "jasperbb")
                {
                    arguments += " -c " + "jasperbigffs";
                }
                else if (boardtype == "trinitybb")
                {
                    arguments += " -c " + "trinitybigffs";
                }
                else if (boardtype == "coronabb")
                {
                    arguments += " -c " + "coronabigffs";
                }
                else if (boardtype == "winchesterbb")
                {
                    arguments += " -c " + "winchesterbigffs";
                }
                else
                {
                    arguments += " -c " + boardtype + "bigffs";
                }
            }
            else
            {
                arguments += " -c " + boardtype;
            }

            if (_xlusb) arguments += " -a xl_usb";
            else if (_xlhdd) arguments += " -a xl_hdd";
            else if (_xlboth) arguments += " -a xl_both";

            foreach (String patch in _patches)
            {
                arguments += " " + patch;
            }
            if (variables.debugMode) arguments += " -v";
            arguments += " -noenter";
            arguments += " -f " + _dash;
            arguments += " -d data";
            arguments += " \"" + variables.xefolder + "\\" + variables.updflash + "\" ";

            RegexOptions options = RegexOptions.None;
            Regex regex = new Regex(@"[ ]{2,}", options);
            arguments = regex.Replace(arguments, @" ");

            if (variables.debugMode) Console.WriteLine(variables.rootfolder);
            if (variables.debugMode) Console.WriteLine("---" + variables.rootfolder + @"\xeBuild\xeBuild.exe");
            if (variables.debugMode) Console.WriteLine(arguments);
            pProcess.StartInfo.Arguments = arguments;
            pProcess.StartInfo.UseShellExecute = false;
            pProcess.StartInfo.WorkingDirectory = variables.rootfolder;
            pProcess.StartInfo.RedirectStandardInput = true;
            pProcess.StartInfo.RedirectStandardOutput = true;
            pProcess.StartInfo.CreateNoWindow = true;
            if (!postBuildActionsAreRequired()) pProcess.Exited += new EventHandler(xeExit);
            //pProcess.OutputDataReceived += new System.Diagnostics.DataReceivedEventHandler(DataReceived);
            //pProcess.Exited += new EventHandler(xe_Exited);
            //pProcess.OutputDataReceived += new System.Diagnostics.DataReceivedEventHandler(process_OutputDataReceived);
            try
            {
                AutoResetEvent outputWaitHandle = new AutoResetEvent(false);
                pProcess.OutputDataReceived += (sender, e) =>
                {
                    if (e.Data == null)
                    {
                        outputWaitHandle.Set();
                    }
                    else
                    {
                        Console.WriteLine(e.Data);
                        if (e.Data != null && e.Data.Contains("image built")) {
                            success = true;
                            if (!postBuildActionsAreRequired())
                            {
                                variables.xefinished = true;
                            }
                        }
                    }
                };
                pProcess.Start();
                pProcess.BeginOutputReadLine();
                pProcess.StandardInput.WriteLine("enter");
                pProcess.WaitForExit();

                if (pProcess.HasExited)
                {
                    pProcess.CancelOutputRead();
                }

                //
                // Any post-build actions on success here
                //
                // Ensure the postBuildActionsAreRequired
                // function is updated if anything is added
                //
                if (success && postBuildActionsAreRequired())
                {
                    if (_xdkbuild && _rgh3)
                    {
                        MainForm.mainForm.XDKbuild.create(boardtype, true);
                        MainForm.mainForm.rgh3Build.create(_ctype.Text, "00000000000000000000000000000000", true);
                    }
                    else if (_xdkbuild && _ttype == variables.hacktypes.glitch2m)
                    {
                        MainForm.mainForm.XDKbuild.create(boardtype);
                    }
                    else if (_ttype == variables.hacktypes.glitch2m && _rgh3)
                    {
                        MainForm.mainForm.rgh3Build.create(_ctype.Text, "00000000000000000000000000000000", true);
                    }    
                    else if (_rgh3)
                    {
                        MainForm.mainForm.rgh3Build.create(_ctype.Text, _cpukey, true);
                    }
                    else
                    {
                        variables.xefinished = true;
                        MainForm.mainForm.xPanel.xeExitActual();
                    }
                }
            }
            catch (Exception objException)
            {
                Console.WriteLine(objException.Message);
            }
        }

        public void build(string arguments) // This takes the input from the custom command, don't apply arguments
        {
            success = false;
            System.Diagnostics.Process pProcess = new System.Diagnostics.Process();
            pProcess.StartInfo.FileName = variables.rootfolder + @"\xeBuild\xeBuild.exe";

            if (!arguments.Contains("-noenter")) arguments += " -noenter";
            if (!arguments.Contains("-p") && variables.cpukey.Length > 0) arguments += " -p " + variables.cpukey;
            if (!arguments.Contains("-d")) arguments += " -d data"; // This breaks sequencing in how J-Runner wraps XeBuild
            else
            {
                Console.WriteLine("Remove -d from your command and try again");
                return;
            }
            
            arguments += " \"" + variables.xefolder + "\\" + variables.updflash + "\" ";

            if (variables.debugMode) Console.WriteLine(variables.rootfolder);
            if (variables.debugMode) Console.WriteLine("---" + variables.rootfolder + @"\xeBuild\xeBuild.exe");
            if (variables.debugMode) Console.WriteLine(arguments);
            pProcess.StartInfo.Arguments = arguments;
            pProcess.StartInfo.UseShellExecute = false;
            pProcess.StartInfo.WorkingDirectory = variables.rootfolder;
            pProcess.StartInfo.RedirectStandardInput = true;
            pProcess.StartInfo.RedirectStandardOutput = true;
            pProcess.StartInfo.CreateNoWindow = true;
            pProcess.Exited += new EventHandler(xeExit);
            //pProcess.OutputDataReceived += new System.Diagnostics.DataReceivedEventHandler(DataReceived);
            //pProcess.Exited += new EventHandler(xe_Exited);
            //pProcess.OutputDataReceived += new System.Diagnostics.DataReceivedEventHandler(process_OutputDataReceived);
            try
            {
                AutoResetEvent outputWaitHandle = new AutoResetEvent(false);
                pProcess.OutputDataReceived += (sender, e) =>
                {
                    if (e.Data == null)
                    {
                        outputWaitHandle.Set();
                    }
                    else
                    {
                        Console.WriteLine(e.Data);
                        if (e.Data != null && e.Data.Contains("image built"))
                        {
                            success = true;
                            if (!(_xdkbuild && _ttype != variables.hacktypes.devgl) && !_rgh3) variables.xefinished = true;
                        }
                    }
                };
                pProcess.Start();
                pProcess.BeginOutputReadLine();
                pProcess.StandardInput.WriteLine("enter");
                pProcess.WaitForExit();

                if (pProcess.HasExited)
                {
                    pProcess.CancelOutputRead();
                }
            }
            catch (Exception objException)
            {
                Console.WriteLine(objException.Message);
            }
        }


        ////////////////////////////////////////////////


        public void Uloadvariables(string dash, variables.hacktypes ttype, List<string> patches, bool altoptions, bool nowrite, bool noava, bool clean, bool noreeb, bool DLpatches, bool includeLaunch)
        {
            this._dash = dash;
            this._ttype = ttype;
            this._patches = patches;
            this._nowrite = nowrite;
            this._noava = noava;
            this._clean = clean;
            this._altoptions = altoptions;
            this._noreeb = noreeb;
            this._DLpatches = DLpatches;
            this._includeLaunch = includeLaunch;
        }

        public XebuildError createxebuild()
        {
            XebuildError result = XebuildError.none;
            if (_dash.Equals("")) result = XebuildError.nodash;
            if (result != XebuildError.none) return result;
            moveOptions();

            Console.WriteLine("Load Files Initiliazation Finished");
            checkDashLaunch();

            Console.WriteLine("Started Updating Console to {0}", _dash);
            variables.xefolder = variables.outfolder;

            return result;
        }

        public void update()
        {
            success = false;
            System.Diagnostics.Process pProcess = new System.Diagnostics.Process();
            pProcess.StartInfo.FileName = variables.rootfolder + @"\xeBuild\xeBuild.exe";
            string arguments = "update ";
            foreach (String patch in _patches)
            {
                arguments += " " + patch;
            }
            if (variables.debugMode) arguments += " -v";
            if (_noava) arguments += " -noava";
            if (_nowrite) arguments += " -nowrite";
            if (_clean) arguments += " -clean";
            if (_noreeb) arguments += " -noreeb";
            arguments += " -noenter";
            arguments += " -f " + _dash;
            arguments += " -d ";
            arguments += "\"" + variables.outfolder + "\"";

            RegexOptions options = RegexOptions.None;
            Regex regex = new Regex(@"[ ]{2,}", options);
            arguments = regex.Replace(arguments, @" ");

            if (variables.debugMode) Console.WriteLine(variables.rootfolder);
            if (variables.debugMode) Console.WriteLine("---" + variables.rootfolder + @"\xeBuild\xeBuild.exe");
            if (variables.debugMode) Console.WriteLine(arguments);
            pProcess.StartInfo.Arguments = arguments;
            pProcess.StartInfo.UseShellExecute = false;
            pProcess.StartInfo.WorkingDirectory = variables.rootfolder;
            pProcess.StartInfo.RedirectStandardInput = true;
            pProcess.StartInfo.RedirectStandardOutput = true;
            pProcess.StartInfo.CreateNoWindow = true;
            pProcess.Exited += new EventHandler(xeExit);
            try
            {
                AutoResetEvent outputWaitHandle = new AutoResetEvent(false);
                pProcess.OutputDataReceived += (sender, e) =>
                {
                    if (e.Data == null)
                    {
                        outputWaitHandle.Set();
                    }
                    else
                    {
                        Console.WriteLine(e.Data);
                        if (e.Data != null && e.Data.Contains("image built"))
                        {
                            success = true;
                            variables.xefinished = true;
                        }
                    }
                };
                pProcess.Start();
                pProcess.BeginOutputReadLine();
                pProcess.WaitForExit();

                if (pProcess.HasExited)
                {
                    pProcess.CancelOutputRead();
                }
            }
            catch (Exception objException)
            {
                Console.WriteLine(objException.Message);
            }
        }

        public void client(string args)
        {
            System.Diagnostics.Process pProcess = new System.Diagnostics.Process();
            pProcess.StartInfo.FileName = variables.rootfolder + @"\xeBuild\xeBuild.exe";
            string arguments = "client ";
            arguments += args;
            if (variables.debugMode) arguments += " -v";
            arguments += " -noenter";

            RegexOptions options = RegexOptions.None;
            Regex regex = new Regex(@"[ ]{2,}", options);
            arguments = regex.Replace(arguments, @" ");

            if (variables.debugMode) Console.WriteLine(variables.rootfolder);
            if (variables.debugMode) Console.WriteLine("---" + variables.rootfolder + @"\xeBuild\xeBuild.exe");
            if (variables.debugMode) Console.WriteLine(arguments);
            pProcess.StartInfo.Arguments = arguments;
            pProcess.StartInfo.UseShellExecute = false;
            pProcess.StartInfo.WorkingDirectory = variables.rootfolder;
            pProcess.StartInfo.RedirectStandardInput = true;
            pProcess.StartInfo.RedirectStandardOutput = true;
            pProcess.StartInfo.CreateNoWindow = true;
            //pProcess.Exited += new EventHandler(xeExit);
            try
            {
                AutoResetEvent outputWaitHandle = new AutoResetEvent(false);
                pProcess.OutputDataReceived += (sender, e) =>
                {
                    if (e.Data == null)
                    {
                        outputWaitHandle.Set();
                    }
                    else
                    {
                        Console.WriteLine(e.Data);
                    }
                };
                pProcess.Start();
                pProcess.BeginOutputReadLine();
                pProcess.WaitForExit();

                if (pProcess.HasExited)
                {
                    pProcess.CancelOutputRead();
                }
            }
            catch (Exception objException)
            {
                Console.WriteLine(objException.Message);
            }


        }

        public delegate void xeExited(object sender, EventArgs e);
        public event xeExited xeExit;


    }
}
